package connect4.network;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

public class Client {
    private static final String USAGE
            = "Usage: <address> <port>";
    private static final String NAME = "client";

    /** Starts a Client application. */
    public static void main(String[] args) {
        if (args.length != 2) {
            System.out.println(USAGE);
            System.exit(0);
        }

        InetAddress addr = null;
        int port = 0;
        Socket sock = null;

        // Check args[0] - the IP-adress
        try {
            addr = InetAddress.getByName(args[0]);
        } catch (UnknownHostException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: host " + args[0] + " unknown");
            System.exit(0);
        }

        // Parse args[1] - the port
        try {
            port = Integer.parseInt(args[1]);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: port " + args[1]
                    + " is not an integer");
            System.exit(0);
        }

        // Try to open a Socket to the server
        try {
            sock = new Socket(addr, port);
        } catch (IOException e) {
            System.out.println("ERROR: could not create a socket on " + addr
                    + " and port " + port);
            System.exit(0);
        }

        // Create Peer object and start the two-way communication
        Thread streamInputHandler = new Thread(client);
        streamInputHandler.start();
        client.handleTerminalInput();
        client.shutDown();
    }

} // end of class Client