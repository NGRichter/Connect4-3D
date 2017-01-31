package connect4.network.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Scanner;

public class ServerStarter extends Thread {

	private static final String USAGE
			= "Usage: <port>";
	private static final String NAME = "server";
	private String port;

	//Constructer to give a port to, used in system testing.
	public ServerStarter(String port) {
		this.port = port;
	}

	public static void main(String[] args) {

		//Test if correct amount of arguments.
		if (args.length != 1) {
			System.out.println(USAGE);
			System.exit(0);
		}
		ServerSocket serversock = null;

		int port = 0;

		//Construct the port
		try {
			port = Integer.parseInt(args[0]);
		} catch (NumberFormatException e) {
			System.err.println("ERROR: port " + args[0]
					+ " is not an integer.");
			System.exit(0);
		}

		//Attempt opening server socket
		while (serversock == null) {
			try {
				serversock = new ServerSocket(port);
			} catch (IOException e) {
				System.err.println("ERROR: Could not create server socket on port "
						+ port);
				Scanner in = new Scanner(System.in);
				System.out.println("Please specify a new port number: ");
				String portnumber = in.nextLine();
				try {
					port = Integer.parseInt(portnumber);
				} catch (NumberFormatException i) {
					System.err.println("ERROR: port " + args[0]
							+ " is not an integer.");
				}
			}
		}

		Server server = new Server();
		Lobby lobby = new Lobby(server);
		server.start();
		System.out.println("Server started on port " + port);
		lobby.start();
		System.out.println("Lobby initialized.");

		//Create server peer object and start two-way communication
		while (true) {
			try {
				Socket sock = serversock.accept();
				ClientHandler clientHandler = new ClientHandler(lobby, sock);
				server.addClient(clientHandler);
				clientHandler.start();
				System.out.println("A client has connected to the server.");
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	//We could do no system test without it being a thread
	public void run() {
		main(new String[]{port});
	}

}
