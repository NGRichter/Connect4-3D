package connect4.network.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

public class ServerStarter {

	private static final String USAGE
			= "Usage: <port>";
	private static final String NAME = "server";


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
		try {
			serversock = new ServerSocket(port);
		} catch (IOException e) {
			System.err.println("ERROR: Could not create server socket on port "
					+ port);
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

}
