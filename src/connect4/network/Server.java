package connect4.network;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class Server extends Thread {
	
	private List<ClientHandler> clients;
	
	public Server() {
		clients = new ArrayList<ClientHandler>();
	}
	
	public void run() {
		while (true) {
			for (ClientHandler client : clients) {
				ClientBuffer buffer = client.getBuffer();
				if (!buffer.isEmpty()) {
					String temp = buffer.readBuffer();
					String[] command = temp.split(" ");
					if (command.length != 0) {
						if (command[0].equals("Join") && command.length >= 2) {
							
						}
					}
				}
			}
		}
	}
	
	public void sendError(ClientHandler client, String errorCode) {
		try {
			client.handleOutput("Error: " + errorCode);
		} catch (IOException e) {
			removeClient(client);
		}
	}
	
	public void addClient(ClientHandler client) {
		if (!clients.contains(client)) {
			clients.add(client);
		}
	}
	
	public void removeClient(ClientHandler client) {
		if (clients.contains(client)) {
			clients.remove(client);
		}
	}

}
