package connect4.network.server;

import connect4.bonus.Score;
import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Game;
import connect4.game.Player;

import java.io.IOException;
import java.util.Calendar;
import java.util.Collections;
import java.util.List;

public class GameHandler extends Thread {

	private /*@ spec_public @*/ Game game;
	private /*@ spec_public @*/ Board board;
	private List<ClientHandler> gamers;
	private /*@ spec_public @*/ ClientHandler next;
	private /*@ spec_public @*/ int[] nextMove = {-1, -1};
	private /*@ spec_public @*/ boolean terminate = false;
	private /*@ spec_public @*/ boolean wantHint = false;

	/**
	 * Makes a new Game.
	 * @param clients - The list of clients that are going to play the game
	 * @param dimension - The dimensions of the game
	 * @param noroof - True if clients want no roof, false if they are the dimension as the roof
	 * @param winCondition - The win condition of the game (default = 4)
	 */
	//@ requires \forall int i; i >= 0 && i < clients.size(); clients.get(i) != null;
	//@ requires dimension > 0 && winCondition > 0 && clients.size() >= 2;
	public GameHandler(List<ClientHandler> clients, int dimension, boolean noroof, int winCondition) {
		if (noroof) {
			board = new Board(dimension, dimension, 1000);
		} else {
			board = new Board(dimension, dimension, dimension);
		}
		Player[] players = new Player[clients.size()];
		int i = 0;
		String message = "";
		for (ClientHandler client : clients) {
			players[i] = client.getPlayer();
			i++;
			message += client.getPlayer().getName() + " ";
		}
		game = new Game(board, players, winCondition);
		gamers = clients;
		System.out.println("A game has started with " + message);
	}

	/**
	 * Returns the game object.
	 * @return Game - Game object
	 */
	//@ ensures game != null;
	public Game getGame() {
		return game;
	}

	/**
	 * Sets a boolean to true so the thread knows the current client wants a hint.
	 * @param client - The client that asks for a hint
	 */
	//@ requires client == next;
	//@ ensures wantHint == true;
	public void wantHint(ClientHandler client) {
		if (client == next) {
			wantHint = true;
		} else {
			try {
				client.handleOutput("Error Not your turn");
			} catch (IOException e) {
				disconnectGame(client);
			}
		}
	}

	/**
	 * Sends a message to all clients participating in the game.
	 */
	public void startGame() {
		String startgame = "StartGame";
		for (ClientHandler client : gamers) {
			startgame += " " + client.getUserName();
		}
		for (ClientHandler client : gamers) {
			try {
				client.handleOutput(startgame);
			} catch (IOException e) {
				System.err.println(client.getUserName() + " not reachable");
				disconnectGame(client);
			}
		}
	}

	/**
	 * Stops the thread
	 */
	//@ ensures terminate == true;
	public void stopGame() {
		terminate = true;
	}

	/**
	 * When a client disconnects or leaves this method is called.
	 * It will send every client a message saying that the game ended.
	 * @param disconnect - Client that disconnected
	 */
	//@ requires disconnect != null;
	public void disconnectGame(ClientHandler disconnect) {
		for (ClientHandler client : gamers) {
			try {
				client.handleOutput("ConnectionLost " + disconnect.getUserName());
				client.inLobby();
				client.outGame();
				client.setGame(null);
				client.getLobby().outGame(client);
			} catch (IOException e) {
				client.getLobby().server.removeClient(client);
			}
		}
		stopGame();
	}

	/**
	 * When the game is over this method will tell everyone who the winner is or if it is a draw.
	 * @param winner - String with the username of the winner or "Draw" if a draw
	 */
	//@ requires winner != null;
	public void gameOver(String winner) {
		if (winner.equals("Draw")) {
			for (ClientHandler client : gamers) {
				try {
					client.handleOutput("GameOver Draw");
					client.inLobby();
					client.outGame();
					client.setGame(null);
					client.getLobby().outGame(client);
				} catch (IOException e) {
					client.getLobby().server.removeClient(client);
				}
			}
		} else {
			for (ClientHandler client : gamers) {
				try {
					client.handleOutput("GameOver Winner " + winner);
					client.inLobby();
					client.outGame();
					client.setGame(null);
					client.getLobby().outGame(client);
				} catch (IOException e) {
					client.getLobby().server.removeClient(client);
				}
			}
		}
		stopGame();
	}

	/**
	 * Method used by the server to set nextMove[] to the next move.
	 * Will only change it if it is the client's turn. 
	 * @param x - The x value of the move
	 * @param y - The y value of the move
	 * @param client - The client that wants to make a move
	 */
	//@ requires client == next && x >= 0 && y >= 0;
	//@ ensures nextMove[0] == x && nextMove[1] == y;
	public void getMove(int x, int y, ClientHandler client) {
		if (client != next) {
			try {
				client.handleOutput("Error It is not your turn.");
			} catch (IOException e) {
				disconnectGame(client);
			}
		} else if (nextMove[0] != -1) {
			try {
				client.handleOutput("Error You already send your command or there is something wrong with the server.");
			} catch (IOException e) {
				disconnectGame(client);
			}
		} else {
			nextMove[0] = x;
			nextMove[1] = y;
		}
	}

	/**
	 * This method will notify all clients of the recent move.
	 * @param x - The x value of the move
	 * @param y - The y value of the move
	 */
	//@ requires x >= 0 && x < board.getDimX() && y >= 0 && y < board.getDimY();
	public void notifyMove(int x, int y) {
		for (ClientHandler client : gamers) {
			try {
				client.handleOutput("NotifyMove " + x + " " + y);
			} catch (IOException e) {
				disconnectGame(client);
			}
		}
	}

	/**
	 * Controller for the game.
	 * Shuffles the playerlist.
	 * Tries to make a move when nextMove[0] is not -1 anymore.
	 * When a move is made set nextMove[0] back to -1 to indicate that the move has been processed.
	 * If the client wants a hint the wantHint boolean becomes true and this thread will give back an x and y value.
	 * If the game is over and there is a winner notify everyone about it.
	 * If the winner has logged in also make a leaderboard score.
	 */
	public void run() {
		int turns = 0;
		Collections.shuffle(gamers);
		startGame();
		int i = 0;
		next = gamers.get(i);
		while (!game.gameOver() && !terminate) {
			if (nextMove[0] != -1) {
				try {
					game.board.setField(nextMove[0], nextMove[1], next.getPlayer());
					notifyMove(nextMove[0], nextMove[1]);
					i++;
					i = i % gamers.size();
					next = gamers.get(i);
					nextMove[0] = -1;
					turns++;
				} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
					try {
						next.handleOutput("Error The spot you specified is either not on the board or has no empty spot above");
						nextMove[0] = -1;
						nextMove[1] = -1;
					} catch (IOException e1) {
						disconnectGame(next);
					}
				}
			} else {
				try {
					if (wantHint) {
						foundHint:
						for(int o= 0; o < game.getWinCondition() - 1; o++) {
							int[] winningMove = game.winningMove(next.getPlayer(), game.getWinCondition() - o);
							if (winningMove[0] != -1) {
								try {
									next.handleOutput("Hint " + winningMove[0] + " " + winningMove[1]);
								} catch (IOException e) {
									disconnectGame(next);
								}
								continue foundHint;
							} else {
								for (Player player : game.getPlayers()) {
									winningMove = game.winningMove(player, game.getWinCondition() - o);
									if (winningMove[0] != -1) {
										try {
											next.handleOutput("Hint " + winningMove[0] + " " + winningMove[1]);
										} catch (IOException e) {
											disconnectGame(next);
										}
										continue foundHint;
									}
								}
							}
						}
					}
					wantHint = false;
					Thread.sleep(100);
				} catch (InterruptedException e) {
					System.err.println("Gamethread has been interrupted.");
				}
			}
		}
		if (terminate) {

		} else {
			Player winner = game.checkWinner();
			if (winner == null) {
				gameOver("Draw");
			} else {
				gameOver(winner.getName());
				for (ClientHandler client : gamers) {
					if (client.getPlayer() == winner && client.getLoggedIn()) {
						int scorevalue = board.getDimX() * board.getDimX() * board.getDimX() * game.getWinCondition() - turns * board.getDimX() * game.getWinCondition();
						if (scorevalue < 0) {
							scorevalue = 0;
						}
						Score score = new Score(Calendar.getInstance().get(Calendar.YEAR),
								Calendar.getInstance().get(Calendar.MONTH),
								Calendar.getInstance().get(Calendar.DAY_OF_MONTH),
								Calendar.getInstance().get(Calendar.HOUR_OF_DAY),
								Calendar.getInstance().get(Calendar.MINUTE),
								scorevalue,
								winner.getName());
						client.getLobby().server.leaderboard.addScore(score);
					}
				}
			}
		}
	}
}
