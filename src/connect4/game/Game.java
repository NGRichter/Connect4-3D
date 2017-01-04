package connect4.game;

import java.util.ArrayList;
import java.util.List;

public class Game {
	
	private List<Player> players = new ArrayList<Player>();
	private List<Colour> colours = Colour.allColours();
	private Board board;
	private int winCondition;
	private Player winner;
	
	public Game(Board board, Player[] players, int win) {
		for (Player player : players) {
			this.players.add(player);
		}
		this.board = board;
		winCondition = win;
	}
	
	public void start() {
		boolean rematch = true;
		while (rematch) {
			int i = 0;
			while(!gameOver()) {
				players.get(i).makeMove(board);
				i++;
				i = i % players.size();
			}
			if (winner != null) {
				System.out.println("Player " + winner + " has won!");
			}
			System.out.println("Draw");		
			rematch = wantRematch();
		}

	}
	
	public void reset() {
		board.empty();
	}
	
	public boolean isWinner(Player player) {
		return false;
	}
	
	public boolean isFull() {
		for (int x = 0; x < board.getDimX(); x++) {
			for (int y = 0; y < board.getDimY(); y++) {
				if (board.getFields()[x][y][board.getDimZ() - 1] == null) {
					return false;
				}
			}
		}
		return true;
	}
	
	public boolean gameOver() {
		for (Player player : players) {
			if (isWinner(player)) {
				winner = player;
				return true;
			}
		}
		return isFull();
	}
	
	public boolean wantRematch() {
		return false;
	}
	
	
}
