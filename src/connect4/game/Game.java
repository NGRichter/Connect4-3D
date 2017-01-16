package connect4.game;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import connect4.exceptions.OutsidePlayingBoardException;

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
			} else {
				System.out.println("Draw");	
			}
			rematch = wantRematch();
		}
		System.out.println("Thanks for playing!");

	}
	
	public void reset() {
		board.empty();
	}
	
	public boolean isWinner(Player player) {
		return false;
	}
	
	public Player checkWinner() {
		try{
			for (int z = 0; z < board.getDimZ(); z++) {
			for (int y = 0; y < board.getDimY(); y++) {
				for (int x = 0; x < board.getDimX(); x++) {
					if (x + winCondition < board.getDimX()) {
						for (int i = 0; i < winCondition; i++) {
							Player winner = board.getField(x + i, y, z);							
						}

						
											
					}
					if (y + winCondition < board.getDimY()) {
						for (int i = 0; i < winCondition; i++) {
							
						}
					}

				}
			}
		}
		} catch (OutsidePlayingBoardException e) {
			System.out.println("Winnercheck went outside the playing board");
		}
		
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
		Scanner in = new Scanner(System.in);
		String input = "";
		while (true) {
			input = in.nextLine();
			if (input != "y" || input != "n") {
				System.out.println("Please type \"y\" or \"n\".");
			} else {
				break;
			}
		}
		if (input.equals("y")) {
			reset();
			return true;
		} else {
			return false;
		}
	}
	
	
}
