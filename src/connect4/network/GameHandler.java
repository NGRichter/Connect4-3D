package connect4.network;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.*;

public class GameHandler extends Thread {
	
	private Game game;
	private Board board;
	private List<ClientHandler> gamers = new ArrayList<ClientHandler>();
	private ClientHandler next;
	private int[] nextMove;
	private boolean terminate = false;
	
	public GameHandler(List<ClientHandler> clients, int dimension, boolean noroof, int winCondition) {
		if (noroof) {
			board = new Board(dimension, dimension, 1000);
		} else {
			board = new Board(dimension, dimension, dimension);			
		}
		Player[] players = new Player[clients.size()];
		int i = 0;
		for (ClientHandler client : clients) {
			players[i] = client.getPlayer();
			i++;
		}
		game = new Game(board, players, winCondition);
		gamers = clients;
		nextMove = new int[2];

	}
	
	public Game getGame() {
		return game;
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
				} catch (IOException e) {
					client.getLobby().server.removeClient(client);
				}
			}
		} else {
			for (ClientHandler client : gamers) {
				try {
					client.handleOutput("GameOver " + winner);
					client.inLobby();
					client.outGame();
					client.setGame(null);
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
		} else if (nextMove[0] != -1){
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
				} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
					try {
						next.handleOutput("Error The spot you specified is either not on the board or has no empty spot above");
					} catch (IOException e1) {
						disconnectGame(next);
					}
				}
			} else {
				try {
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
			}			
		}

	}
}
