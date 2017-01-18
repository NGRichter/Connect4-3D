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
					//No command should be empty
					if (command.length != 0) {
						//Commands that can be done while client is not in lobby
						if (!client.getInLobby()) {
							if (command[0].equals("Join") && command.length >= 2) {
								client.makePlayer(command[1]);
								for (int i = 2; i < command.length; i++) {
									if (command[i].equals("chat")) {
										client.hasChat();
									} else if (command[i].equals("security")) {
										client.hasSecurity();
									} else if (command[i].equals("leaderboard")) {
										client.hasLeaderboard();
									} else if (command[i].equals("challenge")) {
										client.hasChallenge();
									}
								}
							}
							//Commands if client is in lobby
						} else if (client.getInLobby()) {
							if (command[0].equals("Ready")) {
								if (command.length >= 2) {
									int players = Integer.parseInt(command[1]);
									client.setPlayers(players);
								}
								if (command.length >= 3) {
									int dimension = Integer.parseInt(command[2]);
									client.setDimension(dimension);
								}
								if (command.length == 4) {
									client.setNoRoof(true);
								}
								client.getLobby().ready(client);
							} else if (command[0].equals("Chat")) {
								String chatmessage = "Chat " + client.getUserName();
								for (int i = 1; i < command.length; i++) {
									chatmessage += " " + command[i];
								}
								for (ClientHandler chat : clients) {
									if (chat != client && chat.getChat()) {
										try {
											chat.handleOutput(chatmessage);
										} catch (IOException e) {
											removeClient(chat);
										}
									}
								}
							}
							//Commands if client is in game
						} else if (client.getInGame()) {
							if (command[0].equals("Leave")) {
								//TO-DO
							} else if (command[0].equals("Move")) {
								//TO-DO
							}
						} 
					}
				}
			}
		}
	}
	
	public void sendError(ClientHandler client, String errorCode) {
		try {
			client.handleOutput("Error " + errorCode);
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
			client.getLobby().disconnect(client);
			clients.remove(client);
		}
	}

}
