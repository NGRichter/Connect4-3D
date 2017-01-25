package connect4.network.server;

import connect4.bonus.Leaderboard;
import connect4.bonus.Security;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class Server extends Thread {

	private final String ACCOUNTS_FILE_PATH = "Serverdata\\Accounts.txt";
	private final String LEADERBOARD_FILE_PATH = "Serverdata\\Leaderboard.txt";
	public Leaderboard leaderboard;
	private List<ClientHandler> clients;
	private Security security;

	public Server() {
		clients = new ArrayList<>();
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
					showError("Server has been interrupted.");
				}
			}

			for (ClientHandler client : clients) {
				Buffer buffer = client.getBuffer();
				if (!buffer.isEmpty()) {
					String temp = buffer.readBuffer();
					if (client.getUserName() == null) {
						System.out.println(client.getSocket().getInetAddress().getHostAddress() + ": " + temp);
					} else {
						System.out.println(client.getUserName() + ": " + temp);
					}
					String[] command = temp.split(" ");
					//No command should be empty
					if (command.length != 0) {

						//Client wants to join.
						if (command[0].equals("Join") && command.length >= 2) {
							if (client.getInLobby() || client.getInGame()) {
								sendError(client, "You have already joined.");
							}
							client.makePlayer(command[1]);
							client.inLobby();
							client.getLobby().connect(client);
							String lobbyMsg = command[1] + " has joined the lobby";
							if (command.length > 2) {
								lobbyMsg += " with:";
							}
							for (int i = 2; i < command.length; i++) {
								switch (command[i]) {
									case "chat":
										client.hasChat();
										lobbyMsg += " chat";
										break;
									case "security":
										client.hasSecurity();
										lobbyMsg += " security";
										break;
									case "leaderboard":
										client.hasLeaderboard();
										lobbyMsg += " leaderboard";
										break;
									case "challenge":
										client.hasChallenge();
										lobbyMsg += " challenge";
										break;
								}
							}
							lobbyMsg += ".";
							showMessage(lobbyMsg);

							//Client wants to disconnect.
						} else if (command[0].equals("Disconnect")) {
							String clientName = "A client";
							if (client.getPlayer() != null) {
								clientName = client.getPlayer().getName();
							}
							removeClient(client);
							showMessage(clientName + " has disconnected from the server.");

							//Client wants to specify security options.
						} else if (command[0].equals("Security") && command.length == 3) {
							if (!client.getLoggedIn()) {
								boolean login = security.login(command[1], command[2]);
								if (login) {
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

							//Client is ready.
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
								showMessage(client.getPlayer().getName() + " is ready.");
							} else {
								sendError(client, "You are not in the lobby.");
							}

							//Client wants to challenge.
						} else if (command[0].equals("Challenge")) {
							//TODO
						} else if (command[0].equals("ChallengeDenied")) {
							//TODO
						} else if (command[0].equals("ChallengeAccept")) {
							//TODO

							//Client wants to leave the game.
						} else if (command[0].equals("Leave")) {
							//TODO

							//Client wants to make a move.
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

							//Client requests a hint.
						} else if (command[0].equals("Hint")) {
							//TODO

							//Client sends a chat message.
						} else if (command[0].equals("Chat")) {
							String chatmessage = client.getUserName() + ": ";
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

							//Client requests the leaderboard.
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

	public void showError(String error) {
		System.err.println(error);
	}

	public void showMessage(String message) {
		System.out.println(message);
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
			if (client.getInLobby()) {
				client.getLobby().disconnect(client);
			}
			//Mag niet, omdat er door clients wordt geiterate.
			clients.remove(client);
		}
	}

}
