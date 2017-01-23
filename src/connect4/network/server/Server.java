package connect4.network.server;

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
			int o = 0;
			while (clients.isEmpty()) {
				try {
					sleep(250);
				} catch (InterruptedException e) {
					System.out.println("An interrupt has happened");
				}
			}
			for (ClientHandler client : clients) {
				Buffer buffer = client.getBuffer();
				if (!buffer.isEmpty()) {
					String temp = buffer.readBuffer();
					String[] command = temp.split(" ");
					//No command should be empty
					if (command.length != 0) {			
						//Commands that can be done while client is not in lobby and not in-game
						if (!client.getInLobby() && !client.getInGame()) {
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
							} else if (command[0].equals("Login") && command.length == 3) {
								//TO-DO
							} else {
								sendError(client, "Cannot understand: \"" + temp + "\"\nValid commands are: \n\"Join username [chat] [security] [leaderboard] [challenge]\"\n\"Login username password\".");
							}
							//Commands clients can do when they have joined
						} else if (client.getInGame() || client.getInLobby()) {
							//Commands if client is in lobby							
							if (client.getInLobby()) {
								if (command[0].equals("Ready")) {
									if (command.length >= 2) {
										int players = Integer.parseInt(command[1]);
										client.setPlayers(players);
									} else {
										client.setPlayers(2);
									}
									if (command.length >= 3) {
										int dimension = Integer.parseInt(command[2]);
										client.setDimension(dimension);
									} else {
										client.setDimension(4);
									}
									if (command.length >= 4) {
										if (command[3].equals("NoRoof")) {
											client.setNoRoof(true);											
										} else {
											client.setNoRoof(false);
										}

									} else {
										client.setNoRoof(false);
									}
									if (command.length == 5) {
										int winCondition = Integer.parseInt(command[4]);
										client.setWinCondition(winCondition);
									}
									client.getLobby().ready(client);
								} else if (command[0].equals("Challenge")) {
									//TO-DO
								} else if (command[0].equals("ChallengeDenied")) {
									//TO-DO
								} else if (command[0].equals("ChallengeAccept")) {
									//TO-DO
								}
									
								//Commands if client is in-game
							} else if (client.getInGame()) {
								if (command[0].equals("Leave")) {
									//TO-DO
								} else if (command[0].equals("Move")) {
									//TO-DO
								} else if (command[0].equals("Hint")) {
									//TO-DO
								}
							}		 
							//Commands if client is in game
							if (command[0].equals("Chat")) {
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
							} else if (command[0].equals("Leaderboard")) {
								//TO-DO
							}
						}
					}
				} else {
					o++;
				}
			}
			if (o == clients.size()) {
				try {
					sleep(250);
				} catch (InterruptedException e) {
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
