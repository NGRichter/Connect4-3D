package connect4.network.server;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import connect4.bonus.*;

public class Server extends Thread {
	
	private List<ClientHandler> clients;
	private final String ACCOUNTS_FILE_PATH = "Serverdata\\Accounts.txt";
	private final String LEADERBOARD_FILE_PATH = "Serverdata\\Leaderboard.txt";
	private Security security;
	public Leaderboard leaderboard;
	
	public Server() {
		clients = new ArrayList<ClientHandler>();
	}
	
	public void run() {
		security = new Security(ACCOUNTS_FILE_PATH);
		leaderboard = new Leaderboard(LEADERBOARD_FILE_PATH);

		while (true) {
			int o = 0;
			while (clients.isEmpty()) {
				try {
					sleep(250);
				} catch (InterruptedException e) {
					System.err.println("Server has been interruped.");
				}
			}
			for (ClientHandler client : clients) {
				Buffer buffer = client.getBuffer();
				if (!buffer.isEmpty()) {
					String temp = buffer.readBuffer();
                    System.out.println(temp);
					String[] command = temp.split(" ");
					//No command should be empty
					if (command.length != 0) {			
						if (command[0].equals("Join") && command.length >= 2) {
							if (client.getInLobby() || client.getInGame()) {
								sendError(client, "You have already joined.");
							}
							client.makePlayer(command[1]);
							client.inLobby();
							client.getLobby().connect(client);
                            System.out.println("Player " + command[1] + " has joined the lobby.");
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
						} else if (command[0].equals("Disconnect")) {
							removeClient(client);
						} else if (command[0].equals("Security") && command.length == 3) {
							if (!client.getLoggedIn()) {
							boolean login = security.login(command[1], command[2]);
							if (login == true) {
								client.loggedIn();
								try {
									client.handleOutput("Security LoginSuccess");
								} catch (IOException e) {
									removeClient(client);
								}
							} else {
								try {
									client.handleOutput("Security LoginDenied");
								} catch (IOException e) {
									removeClient(client);
								}
							}									
							} else {
								sendError(client, "Already logged in.");
							}
						} else if (command[0].equals("Ready")) {
							if (client.getInLobby()) {
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
							} else {
								sendError(client, "You are not in the lobby.");
							}
							
						} else if (command[0].equals("Challenge")) {
							//TO-DO
						} else if (command[0].equals("ChallengeDenied")) {
							//TO-DO
						} else if (command[0].equals("ChallengeAccept")) {
							//TO-DO
						} else if (command[0].equals("Leave")) {
							//TO-DO
						} else if (command[0].equals("Move")) {
							if (client.getGame() != null) {
								try {
									int x = Integer.parseInt(command[1]);
									int y = Integer.parseInt(command[2]);
									client.getGame().getMove(x, y, client);
								} catch (NumberFormatException e) {
									sendError(client, "Invalid syntax please send integers.");
								}
							}
						} else if (command[0].equals("Hint")) {
							//TO-DO		 
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
						} else if (command[0].equals("Leaderboard")) {
							String leaderboardtemp = "Leaderboard";
							String[] leaderboardarraytemp = leaderboard.topN(10).split(" ");
							for (int i = 0; i < leaderboardarraytemp.length; i += 4) {
								leaderboardtemp += " " + leaderboardarraytemp[i] + " " + leaderboardarraytemp[i + 1];
							}
							try {
								client.handleOutput(leaderboardtemp);
							} catch (IOException e) {
								removeClient(client);
							}
						} else {
							sendError(client, "cannot understand: \"" + temp + "\"");
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
			client.handleOutput(errorCode);
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
