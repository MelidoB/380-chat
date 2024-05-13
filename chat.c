#include <gtk/gtk.h>
#include <glib/gunicode.h> /* for utf8 strlen */
#include <sys/socket.h>
#include <netinet/in.h>
#include <gmp.h>
#include <netdb.h>
#include <openssl/sha.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <getopt.h>
#include <openssl/err.h>
#include "dh.h"
#include "keys.h"

#ifndef PATH_MAX
#define PATH_MAX 1024
#endif

#define MASTER_LEN 32
#define MAX_MESSAGE_SIZE 512
#define MAC_LEN 32

struct dhKey myKey;
struct dhKey yourKey;
static unsigned char MasterKey[MASTER_LEN];

static unsigned char *randMe, *randYou; // Initializtion Vector (0 - 15)
static unsigned char *enkme, *enkyou;   // Encryption Keys (16-47)
static unsigned char *macme, *macyou;   // MAC (32-47)

EVP_CIPHER_CTX* csend = NULL;
EVP_CIPHER_CTX* crecv = NULL;

static GtkTextBuffer* tbuf; /* transcript buffer */
static GtkTextBuffer* mbuf; /* message buffer */
static GtkTextView*  tview; /* view for transcript */
static GtkTextMark*   mark; /* used for scrolling to end of transcript, etc */

static int port = 1337;
static char hostname[HOST_NAME_MAX+1] = "localhost";

static pthread_t trecv;     /* wait for incoming messagess and post to queue */
void* recvMsg(void*);       /* for trecv */

#define max(a, bs)         \
        ({ typeof(a) _a = a;    \
         typeof(b) _b = b;    \
         _a > _b ? _a : _b; })

/* network stuff... */

static int listensock, sockfd;
static int isclient = 1;

static void error(const char *msg)
{
        perror(msg);
        exit(EXIT_FAILURE);
}

int initServerNet(int port)
{
        int reuse = 1;
        struct sockaddr_in serv_addr;
        listensock = socket(AF_INET, SOCK_STREAM, 0);
        setsockopt(listensock, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse));
        /* NOTE: might not need the above if you make sure the client closes first */
        if (listensock < 0)
                error("ERROR opening socket");
        bzero((char *) &serv_addr, sizeof(serv_addr));
        serv_addr.sin_family = AF_INET;
        serv_addr.sin_addr.s_addr = INADDR_ANY;
        serv_addr.sin_port = htons(port);
        if (bind(listensock, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) < 0)
                error("ERROR on binding");
        fprintf(stderr, "listening on port %i...\n",port);
        listen(listensock,1);
        socklen_t clilen;
        struct sockaddr_in  cli_addr;
        sockfd = accept(listensock, (struct sockaddr *) &cli_addr, &clilen);
        if (sockfd < 0)
                error("error on accept");
        close(listensock);
        fprintf(stderr, "connection made, starting session...\n");
         /* at this point, should be able to send/recv on sockfd */
        return 0;
}

static int initClientNet(char* hostname, int port)
{
        struct sockaddr_in serv_addr;
        sockfd = socket(AF_INET, SOCK_STREAM, 0);
        struct hostent *server;
        if (sockfd < 0)
                error("ERROR opening socket");
        server = gethostbyname(hostname);
        if (server == NULL) {
                fprintf(stderr,"ERROR, no such host\n");
                exit(0);
        }
        bzero((char *) &serv_addr, sizeof(serv_addr));
        serv_addr.sin_family = AF_INET;
        memcpy(&serv_addr.sin_addr.s_addr,server->h_addr,server->h_length);
        serv_addr.sin_port = htons(port);
        if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
                error("ERROR connecting");
        /* at this point, should be able to send/recv on sockfd */
        return 0;
}
static int shutdownNetwork()
{
        shutdown(sockfd,2);
        unsigned char dummy[64];
        ssize_t r;
        do {
                r = recv(sockfd,dummy,64,0);
        } while (r != 0 && r != -1);
        close(sockfd);
        return 0;
}

/* end network stuff. */


static const char* usage =
"Usage: %s [OPTIONS]...\n"
"Secure chat (CCNY computer security project).\n\n"
"   -c, --connect HOST  Attempt a connection to HOST.\n"
"   -l, --listen        Listen for new connections.\n"
"   -p, --port    PORT  Listen or connect on PORT (defaults to 1337).\n"
"   -h, --help          show this message and exit.\n";

/* Append message to transcript with optional styling.  NOTE: tagnames, if not
 * NULL, must have it's last pointer be NULL to denote its end.  We also require
 * that messsage is a NULL terminated string.  If ensurenewline is non-zero, then
 * a newline may be added at the end of the string (possibly overwriting the \0
 * char!) and the view will be scrolled to ensure the added line is visible.  */
 
 static void tsappend(char* message, char** tagnames, int ensurenewline)
{
        GtkTextIter t0;
        gtk_text_buffer_get_end_iter(tbuf,&t0);
        size_t len = g_utf8_strlen(message,-1);
        if (ensurenewline && message[len-1] != '\n')
                message[len++] = '\n';
        gtk_text_buffer_insert(tbuf,&t0,message,len);
        GtkTextIter t1;
        gtk_text_buffer_get_end_iter(tbuf,&t1);
        /* Insertion of text may have invalidated t0, so recompute: */
        t0 = t1;
        gtk_text_iter_backward_chars(&t0,len);
        if (tagnames) {
                char** tag = tagnames;
                while (*tag) {
                        gtk_text_buffer_apply_tag_by_name(tbuf,*tag,&t0,&t1);
                        tag++;
                }
        }
        if (!ensurenewline) return;
        gtk_text_buffer_add_mark(tbuf,mark,&t1);
        gtk_text_view_scroll_to_mark(tview,mark,0.0,0,0.0,0.0);
        gtk_text_buffer_delete_mark(tbuf,mark);
}

static void sendMessage(GtkWidget* w /* <-- msg entry widget */, gpointer /* data */)
{
        // csend and macmine are initialized in the performHandshake function

        // Get the message from the GTK text buffer
        GtkTextIter mstart; /* start of message pointer */
        GtkTextIter mend;   /* end of message pointer */
        gtk_text_buffer_get_start_iter(mbuf, &mstart);
        gtk_text_buffer_get_end_iter(mbuf, &mend);
        char* message = gtk_text_buffer_get_text(mbuf, &mstart, &mend, 1);

        // Encrypt the message
        unsigned char encryptedMessage[MAX_MESSAGE_SIZE];
        int encryptedLen = 0;

        if (1 != EVP_EncryptUpdate(csend, encryptedMessage, &encryptedLen, (const unsigned char*)message, strlen(message))) {
                ERR_print_errors_fp(stderr);
                return;
        }

        // Generate MAC for the message
        unsigned char mac[MAC_LEN];

        HMAC(EVP_sha256(), macme, MAC_LEN, (const unsigned char*)message, strlen(message), mac, 0);
        
        
        // Send the encrypted message along with the MAC
        ssize_t nbytes;
        if ((nbytes = send(sockfd, encryptedMessage, encryptedLen, 0)) == -1) {
                error("send failed");
                return;
        }

        if ((nbytes = send(sockfd, mac, MAC_LEN, 0)) == -1) {
                error("send failed");
                return;
        }
        
        // Display the original message in the local UI
        char* tags[2] = {"self", NULL};
        tsappend("me: ", tags, 0);
        tsappend(message, NULL, 1);

        // Free dynamically allocated memory
        free(message);
        free(encryptedMessage);

        /* clear message text and reset focus */
        gtk_text_buffer_delete(mbuf, &mstart, &mend);
        gtk_widget_grab_focus(w);
}

static gboolean shownewmessage(gpointer msg)
{
        char* tags[2] = {"friend",NULL};
        char* friendname = "mr. friend: ";
        tsappend(friendname,tags,0);
        char* message = (char*)msg;
        tsappend(message,NULL,1);
        free(message);
        return 0;
}

void showStatusMessage(char* message)
{
    char* tags[2] = {"status", NULL};
    tsappend(message, tags, 1);
}

int performHandshake()
{
        struct dhKey X,Y;
        initKey(&X);
        initKey(&Y);
        dhGen(X.SK,X.PK); // Generate public-private key pair X

        //Exchange Public Keys
        if (isclient)
        {
                //Client sends its public key
                send(sockfd, X.PK,mpz_sizeinbase(X.PK,2),0);

                //Client receives the server's public key
                mpz_t receivedKey;
                mpz_init(receivedKey);
                size_t keySize =  recv(sockfd,receivedKey,MASTER_LEN,0);

                //Store Y.PK as receivedKey
                mpz_set(Y.PK, receivedKey);
                mpz_clear(receivedKey);
        } else {
                //Server receives the client's public key
                mpz_t receivedKey;
                mpz_init(receivedKey);
                size_t keySize = recv(sockfd,receivedKey,MASTER_LEN,0);
                 //Store Y.PK as receivedKey
                mpz_set(Y.PK,receivedKey);
                mpz_clear(receivedKey);

                //Server sends it public
                send(sockfd,X.PK,mpz_sizeinbase(X.PK,2),0);
        }

        //Perform 3DH key exchange and derive keys
        dh3Final(myKey.SK, myKey.PK, X.SK, X.PK, yourKey.PK, Y.PK, MasterKey, MASTER_LEN);

        //Setting pointers IV, encryption, and MAC Keys
        //Since MasterKey size is 32
        randMe = MasterKey + isclient * 16;
        randYou = MasterKey + (1 - isclient) * 16;
        enkme = MasterKey + 16 + isclient * 16;
        enkyou = MasterKey + 16 + (1 - isclient) * 16;
        macme = MasterKey + 32 + isclient * 16;
        macyou = MasterKey + 32 +(1 - isclient) * 16;

        //Initialize encryptions
        csend = EVP_CIPHER_CTX_new();
        crecv = EVP_CIPHER_CTX_new();
        
        /*
         * Initialize encryption context --
         * this will initialize the context for the specified encryption/decryption algotithm and
         * set up the master key and IV for encryption/decryption
         */

        if (1 != EVP_EncryptInit_ex(csend,EVP_aes_256_ctr(),0,enkme,randMe))
        {
                ERR_print_errors_fp(stderr);
        }

        if (1 != EVP_DecryptInit_ex(crecv, EVP_aes_256_ctr(),0,enkyou,randYou))
        {
                ERR_print_errors_fp(stderr);
        }

        //Clean up sensitive key material from memory for security reasons
        shredKey(&X);
        shredKey(&Y);

        return 0; // Successful
}
int main(int argc, char *argv[])
{
        if (init("params") != 0) {
                fprintf(stderr, "could not read DH params from file 'params'\n");
                return 1;
        }
        // define long options
        static struct option long_opts[] = {
                {"connect",  required_argument, 0, 'c'},
                {"listen",   no_argument,       0, 'l'},
                {"port",     required_argument, 0, 'p'},
                {"help",     no_argument,       0, 'h'},
                {0,0,0,0}
        };
        // process options:
        char c;
        int opt_index = 0;
        int port = 1337;
        char hostname[HOST_NAME_MAX+1] = "localhost";
        hostname[HOST_NAME_MAX]=0;
 while ((c = getopt_long(argc, argv, "c:lp:h", long_opts, &opt_index)) != -1) {
                switch (c) {
                        case 'c':
                                if (strnlen(optarg,HOST_NAME_MAX))
                                        strncpy(hostname,optarg,HOST_NAME_MAX);
                                break;
                        case 'l':
                                isclient = 0;
                                break;
                        case 'p':
                                port = atoi(optarg);
                                break;
                        case 'h':
                                printf(usage,argv[0]);
                                return 0;
                        case '?':
                                printf(usage,argv[0]);
                                return 1;
                }
        }
         /* NOTE: might want to start this after gtk is initializ
ed so you can
         * show the messages in the main window instead of stderr/stdout.  If
         * you decide to give that a try, this might be of use:
         * https://docs.gtk.org/gtk4/func.is_initialized.html */

        /* setup GTK... */
        GtkBuilder* builder;
        GObject* window;
        GObject* button;
        GObject* transcript;
        GObject* message;
        GError* error = NULL;
        gtk_init(&argc, &argv);
        builder = gtk_builder_new();
        if (gtk_builder_add_from_file(builder,"layout.ui",&error) == 0) {
                g_printerr("Error reading %s\n", error->message);
                g_clear_error(&error);
                return 1;
        }
         mark  = gtk_text_mark_new(NULL,TRUE);
        window = gtk_builder_get_object(builder,"window");
        g_signal_connect(window, "destroy", G_CALLBACK(gtk_main_quit), NULL);
        transcript = gtk_builder_get_object(builder, "transcript");
        tview = GTK_TEXT_VIEW(transcript);
        message = gtk_builder_get_object(builder, "message");
        tbuf = gtk_text_view_get_buffer(tview);
        mbuf = gtk_text_view_get_buffer(GTK_TEXT_VIEW(message));        button = gtk_builder_get_object(builder, "send");
        g_signal_connect_swapped(button, "clicked", G_CALLBACK(sendMessage), GTK_WIDGET(message));
        gtk_widget_grab_focus(GTK_WIDGET(message));
        GtkCssProvider* css = gtk_css_provider_new();
        gtk_css_provider_load_from_path(css,"colors.css",NULL);
        gtk_style_context_add_provider_for_screen(gdk_screen_get_default(),
                        GTK_STYLE_PROVIDER(css),
                        GTK_STYLE_PROVIDER_PRIORITY_USER);

        /* setup styling tags for transcript text buffer */
        gtk_text_buffer_create_tag(tbuf,"status","foreground","#657b83","font","italic",NULL);
        gtk_text_buffer_create_tag(tbuf,"friend","foreground","#6c71c4","font","bold",NULL);
         /* start receiver thread: */
        if (pthread_create(&trecv,0,recvMsg,0)) {
                fprintf(stderr, "Failed to create update thread.\n");
        }

        gtk_main();

        shutdownNetwork();
        return 0;
}

/* thread function to listen for new messages and post them to the gtk
 * main loop for processing: */
void* recvMsg(void*)
{
        char msg[MAX_MESSAGE_SIZE + 2]; /* might add \n and \0 */
        ssize_t nbytes;

        if(isclient){
                initClientNet(hostname,port);
        }
        else{
                initServerNet(port);
        }
        performHandshake();
         while (1) {
                // Receive the encrypted message
                if ((nbytes = recv(sockfd, msg, MAX_MESSAGE_SIZE, 0)) == -1) {
                        perror("recv failed");
                        // Handle the error appropriately
                        showStatusMessage("Error receiving message");
                        return 0;
                }

                if (nbytes == 0) {
                        // The other side has disconnected
                        showStatusMessage("The other side has disconnected");
                        return 0;
                }

                // Receive the MAC
                unsigned char receivedMac[MAC_LEN];
                if ((nbytes = recv(sockfd, receivedMac, MAC_LEN, 0)) == -1) {
                        perror("recv failed");
                        // Handle the error appropriately
                        showStatusMessage("Error receiving MAC");
                        return 0;
                }
                 // Decrypt the message
                unsigned char decryptedMessage[MAX_MESSAGE_SIZE+MAC_LEN];
                int decryptedLen = 0;

                if (1 != EVP_DecryptUpdate(crecv, decryptedMessage, &decryptedLen, (const unsigned char*)msg, nbytes)) {
                        ERR_print_errors_fp(stderr);
                        // Handle decryption error (log error, show status message, etc.)
                        showStatusMessage("Error decrypting message");
                        return 0;
                }
                // Verify MAC
                unsigned char computedMac[MAC_LEN];
                HMAC(EVP_sha256(), macyou, 16, (const unsigned char*)decryptedMessage, decryptedLen, computedMac, NULL);

                if (memcmp(receivedMac, computedMac, MAC_LEN) != 0) {
                        // Handle MAC verification failure
                        fprintf(stderr, "MAC verification failed\n");
                        showStatusMessage("MAC verification failed");
                        return 0;
                }
            // Process the decrypted message
                char* m = malloc(decryptedLen + 2);
                memcpy(m, decryptedMessage, decryptedLen);
                if (m[decryptedLen - 1] != '\n')
                        m[decryptedLen++] = '\n';
                m[decryptedLen] = 0;

                // Show the message in the GTK main loop
                g_main_context_invoke(NULL, shownewmessage, (gpointer)m);

        }
        return 0;
}

