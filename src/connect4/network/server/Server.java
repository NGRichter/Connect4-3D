package connect4.network.server;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import connect4.bonus.Challenge;
import connect4.bonus.Leaderboard;
import connect4.bonus.Security;

public class Server extends Thread {

	private final String ACCOUNTS_FILE_PATH = "Serverdata\\Accounts.txt";
	private final String LEADERBOARD_FILE_PATH = "Serverdata\\Leaderboard.txt";
	public Leaderboard leaderboard;
	private /*@ spec_public @*/ List<ClientHandler> clients;
	private /*@ spec_public @*/ List<ClientHandler> toBeRemoved = new ArrayList<>();
	private Security security;

	public Server() {
		clients = new ArrayList<>();
	}

	/**
	 * Runs through the buffers of all the clients connected to see if they have send anything.
	 * If clients have send anything process them accordingly.
	 */
	public void run() {
		security = new Security(ACCOUNTS_FILE_PATH);
		leaderboard = new Leaderboard(LEADERBOARD_FILE_PATH);
		long beginTime = System.currentTimeMillis();

		while (true) {

			long endTime = System.currentTimeMillis();
			if(endTime - beginTime >= 60000) {
				if (clients.size() == 1) {
					System.out.println("1 client is currently connected.");
				} else {
					System.out.println(clients.size() + " clients are currently connected.");
				}

				beginTime = endTime;
			}

			int empty = 0;//Counter to see if no client has send anything.
			//Sleep if there are no clients (otherwise cpu goes to 30% used).
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
					String[] command = temp.split(" ");
					if (client.getUserName() == null) {
						if (command[0].equals("Security") && command.length == 3) {
							showMessage(client.getSocket().getInetAddress().getHostAddress() + ": " + command[0] + " " + command[1] + " ******");
						} else {
							showMessage(client.getSocket().getInetAddress().getHostAddress() + ": " + temp);
						}
					} else {
						if (command[0].equals("Security") && command.length == 3) {
							showMessage(client.getUserName() + ": " + command[0] + " " + command[1] + " ******");
						} else {
							showMessage(client.getUserName() + ": " + temp);
						}
					}

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
									sendMessage(client, "Security LoginSuccess");
								} else {
									sendMessage(client, "Security LoginDenied");
								}
							} else {
								sendError(client, "Already logged in.");
							}

							//Client is ready.
						} else if (command[0].equals("Ready")) {
							if (client.getInLobby() && !client.getHasBeenChallenged()) {
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
								sendError(client, "You are not in the lobby or you have been challenged.");
							}

							//Client wants to challenge.
						} else if (command[0].equals("Challenge")) {
							if (!client.getInGame() && !client.getHasBeenChallenged()) {
								if (command.length >= 4) {
									int dimension = Integer.parseInt(command[1]);
									int players = Integer.parseInt(command[2]);
									if (command[3].equals("NoRoof")) {
										if (command.length == 4 + players - 1) {
											List<ClientHandler> challenge = new ArrayList<>();
											for (ClientHandler player : clients) {
												if (player.getInLobby() && !player.getHasBeenChallenged() && player.getChallenge()) {
													for (int i = 4; i < command.length; i++) {
														if (player.getUserName().equalsIgnoreCase(command[i])) {
															challenge.add(player);
															break;
														}
													}
												}
											}
											if (challenge.size() == players - 1) {
												Challenge newChallenge = new Challenge(challenge, dimension, true, client);
												newChallenge.start();
											} else {
												sendError(client, "Not all people specified are available or exist");
											}
										} else {
											sendError(client, "Amount of players does not correspond with the amount of usernames");
										}
									} else {
										if (command.length == 3 + players - 1) {
											List<ClientHandler> challenge = new ArrayList<>();
											for (ClientHandler player : clients) {
												if (player.getInLobby() && !player.getHasBeenChallenged() && player.getChallenge()) {
													for (int i = 3; i < command.length; i++) {
														if (player.getUserName().equalsIgnoreCase(command[i])) {
															challenge.add(player);
															break;
														}
													}
												}
											}
											if (challenge.size() == players - 1) {
												Challenge newChallenge = new Challenge(challenge, dimension, false, client);
												newChallenge.start();
											} else {
												sendError(client, "Not all people specified are available or exist");
											}
										} else {
											sendError(client, "Amount of players does not correspond with the amount of usernames");
										}
									}
								} else {
									sendError(client, "Please use Challenge <dimension> <amount of players> [NoRoof] <username1> <username2> ...");
								}
							}
						//Client wants to accept or deny challenge
						} else if (command[0].equals("ChallengeAccept") && command.length == 2) {
							if (command[1].equals("y") || command[1].equals("yes")) {
								client.getChallengeGame().acceptChallenge(client);
							} else if (command[1].equals("n") || command[1].equals("no")) {
								client.getChallengeGame().denyChallenge(client);
							} else {
								sendError(client, "Cannot understand " + command[1]);
							}
						//Client wants to see which players he can challenge
						} else if (command[0].equals("GetPlayers")) {
							String players = "Players";
							for (ClientHandler player : clients) {
								if (player.getChallenge() && !player.getInGame() && !player.getHasBeenChallenged()) {
									players +=  " " + player.getUserName();
								}
							}
							sendMessage(client, players);
						//Used only by our client, to see everybody that is in the lobby and in game
						} else if (command[0].equals("GetAllPlayers")) {
							String players = "AllPlayers";
							for (ClientHandler player : clients) {
								if (player.getInLobby()) {
									players +=  " " + player.getUserName();
								}
							}
							players += " Game";
							for (ClientHandler player : clients) {
								if (player.getInGame()) {
									players += " " + player.getUserName();
								}
							}
							sendMessage(client, players);

							//Client wants to leave the game.
						} else if (command[0].equals("Leave")) {
							if (client.getGame() != null) {
								client.getGame().disconnectGame(client);
							} else {
								sendError(client, "You are not in a game");
							}

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
							} else {
								sendError(client, "You are not in a game");
							}

							//Client requests a hint.
						} else if (command[0].equals("Hint")) {
							if (client.getGame() != null) {
								client.getGame().wantHint(client);
							}

							//Client sends a chat message.
						} else if (command[0].equals("Chat") && client.getChat()) {
							String chatMessage = client.getUserName() + ": ";
							for (int i = 1; i < command.length; i++) {
								chatMessage += " " + command[i];
							}
							for (ClientHandler chat : clients) {
								if (chat != client && chat.getChat()) {
									sendMessage(chat, chatMessage);
								}
							}

							//Client requests the leaderboard.
						} else if (command[0].equals("Leaderboard")) {
							String leaderboardTemp = "Leaderboard";
							showMessage(leaderboard.topN(10));
							String[] leaderboardArrayTemp = leaderboard.topN(10).split(" ");
							for (int i = 0; i < leaderboardArrayTemp.length; i += 4) {
								leaderboardTemp += " " + leaderboardArrayTemp[i] + " " + leaderboardArrayTemp[i + 1];
							}
							sendMessage(client, leaderboardTemp);

						} else {
							sendError(client, "cannot understand: \"" + temp + "\"");
						}
					}
				} else {
					empty++;
				}
			}
			if (empty == clients.size()) {
				try {
					for (ClientHandler remove : toBeRemoved) {
						clients.remove(remove);
						remove.getLobby().disconnect(remove);

					}
					sleep(250);
				} catch (InterruptedException e) {
				}
			}
		}
	}

	/**
	 * Send an error message to the System.err console.
	 * @param error - String with error message
	 */
	public void showError(String error) {
		System.err.println(error);
	}

	/**
	 * Send an message to the normal server console.
	 * @param message - String with message
	 */
	public void showMessage(String message) {
		System.out.println(message);
	}

	/**
	 * Send an error message to the client.
	 * @param client - The client you want to send an error message to
	 * @param errorCode - The error message to want to send
	 */
	//@ requires client != null;
	public void sendError(ClientHandler client, String errorCode) {
		try {
			client.handleOutput("Error " + errorCode);
		} catch (IOException e) {
			removeClient(client);
		}
	}

	/**
	 * Send a message to a client.
	 * @param client - The client you want to send an error message to
	 * @param message - The message to want to send
	 */
	//@ requires client != null;
	public void sendMessage(ClientHandler client, String message) {
		try {
			client.handleOutput(message);
		} catch (IOException e) {
			removeClient(client);
		}
	}

	/**
	 * Adds a client to the list of clients
	 * Used by the ServerStarter
	 * @param client - The client you want to add
	 */
	//@ ensures clients.contains(client);
	public void addClient(ClientHandler client) {
		if (!clients.contains(client)) {
			clients.add(client);
		}
	}

	/**
	 * If you want a client removed you use this method.
	 * It will remove the client when the server is not busy
	 * scrolling through the clients.
	 * @param client - The client you want removed
	 */
	//@ ensures toBeRemoved.contains(client);
	public void removeClient(ClientHandler client) {
		toBeRemoved.add(client);
		client.getLobby().disconnect(client);
	}

}
