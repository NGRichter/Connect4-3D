package connect4.network;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;

public class Server {

    private static final String USAGE
            = "Usage: <port>";
    private static final String NAME = "server";


    public static void main(String[] args){

        //Test if correct amount of arguments.
        if (args.length != 1){
            System.out.println(USAGE);
            System.exit(0);
        }
        ServerSocket serversock = null;

        int port = 0;

        //Construct the port
        try {
            port = Integer.parseInt(args[0]);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: port " + args[0]
                    + " is not an integer");
            System.exit(0);
        }

        //Attempt opening server socket
        try {
            serversock = new ServerSocket(port);
        } catch (IOException e) {
            System.out.println("ERROR: Could not create server socket on port "
                    + port);
        }

        //Create server peer object and start two-way communication
        try {
            Socket sock = serversock.accept();
            Peer serverpeer = new Peer(NAME, sock);
            Thread streamInputHandler = new Thread(serverpeer);
            streamInputHandler.start();
            serverpeer.handleTerminalInput();
            serverpeer.shutDown();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }


}
