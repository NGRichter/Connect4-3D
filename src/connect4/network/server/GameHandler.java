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

	private Game game;
	private Board board;
	private List<ClientHandler> gamers;
	private ClientHandler next;
	private int[] nextMove = {-1, -1};
	private boolean terminate = false;
	private boolean wantHint = false;

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

	public Game getGame() {
		return game;
	}

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
			}
		}
	}

	public void stopGame() {
		terminate = true;
	}

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

	public void notifyMove(int x, int y) {
		for (ClientHandler client : gamers) {
			try {
				client.handleOutput("NotifyMove " + x + " " + y);
			} catch (IOException e) {
				disconnectGame(client);
			}
		}
	}

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
