package connect4.game;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;

public class Game {
	
	private List<Player> players = new ArrayList<Player>();
	private List<Colour> colours = Colour.allColours();
	public Board board;
	private int winCondition;
	
	public Game(Board board, Player[] players, int win) {
		for (Player player : players) {
			this.players.add(player);
		}
		this.board = board;
		winCondition = win;
	}
	
	public void start() {
		Player winner;
		boolean rematch = true;
		while (rematch) {
			int i = 0;
			while(!gameOver()) {
                board.drawLayer(0);
                players.get(i).makeMove(this);
				i++;
				i = i % players.size();
			}
			if ((winner = checkWinner()) != null) {
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
		Player winner = checkWinner();
		if (winner == player) {
			return true;
		} else {
			return false;
		}
	}
	
	public Player checkWinner() {
		try{
			for (int z = 0; z < board.getDimZ(); z++) {
				for (int y = 0; y < board.getDimY(); y++) {
					for (int x = 0; x < board.getDimX(); x++) {
						if (board.getField(x, y, z) != null) {
							if (x + winCondition - 1 < board.getDimX()) {//If there are enough spaces to the right.
								for (int i = 0; i < winCondition - 1; i++) {//For every space to the right check if it is the same as the next one.
									if (board.getField(x + i, y, z) == board.getField(x + i + 1, y, z)) {
										if (i + 1 == winCondition - 1) {
											return board.getField(x, y, z);
										}
									} else {
										break;
									}
								}
								if (y + winCondition - 1 < board.getDimY()) {
									for (int i = 0; i < winCondition - 1; i++) {
										if (board.getField(x + i, y + i, z) == board.getField(x + i + 1, y + i + 1, z)) {
											if (i + 1 == winCondition - 1) {
												return board.getField(x, y, z);
											}
										} else {
											break;
										}
									}
								}
								if (z + winCondition - 1 < board.getDimZ()) {//If there are enough spaces up also check the diagonal up/right.
									for (int i = 0; i < winCondition -1; i++) {
										if (board.getField(x + i, y, z + i) == board.getField(x + i + 1, y, z + i + 1)) {
											if (i + 1 == winCondition - 1) {
												return board.getField(x, y, z);
											}
										} else {
											break;
										}
									}
									if (y + winCondition - 1 < board.getDimY()) {//If in all directions there is enough space. (to the right, bottom (y++) and up)
										for (int i = 0; i < winCondition - 1; i++) {
											if (board.getField(x + i, y + i, z + i) == board.getField(x + i + 1, y + i + 1, z + i + 1)) {
												if (i + 1 == winCondition - 1) {
													return board.getField(x, y, z);
												}
											} else {
												break;
											}
										}
									}
									if (y - winCondition + 1 >= 0) {//If in all directions there is enough space. (to the right, top (y--) and up)
										for (int i = 0; i < winCondition - 1; i++) {
											if (board.getField(x + i, y - i, z + i) == board.getField(x + i + 1, y - i - 1, z + i + 1)) {
												if (i + 1 == winCondition - 1) {
													return board.getField(x, y, z);
												}
											} else {
												break;
											}
										}
									}
									
								}
								
							}
							
							
							
							if (y + winCondition - 1 < board.getDimY()) {//If there are enough spaces to the bottom.
								for (int i = 0; i < winCondition - 1; i++) {
									if (board.getField(x, y + i, z) == board.getField(x, y + i + 1, z)) {
										if (i + 1 == winCondition - 1) {
											return board.getField(x, y, z);
										}
									} else {
										break;
									}
								}
								if (x - winCondition + 1 >= 0) {
									for (int i = 0; i < winCondition - 1; i++) {
										if (board.getField(x - i, y + i, z) == board.getField(x - i - 1, y + i + 1, z)) {
											if (i + 1 == winCondition - 1) {
												return board.getField(x, y, z);
											}
										} else {
											break;
										}
									}
									if (z + winCondition - 1 < board.getDimZ()) {
										for (int i = 0; i < winCondition - 1; i++) {
											if (board.getField(x - i, y + i, z + i) == board.getField(x - i - 1, y + i + 1, z + i + 1)) {
												if (i + 1 == winCondition - 1) {
													return board.getField(x, y, z);
												}
											} else {
												break;
											}
										}
									}
								}
								if (z + winCondition - 1 < board.getDimZ()) {
									for (int i = 0; i < winCondition - 1; i++) {
										if (board.getField(x, y + i, z + i) == board.getField(x, y + i + 1, z + i + 1)) {
											if (i + 1 == winCondition - 1) {
												return board.getField(x, y, z);
											}
										} else {
											break;
										}
									}
								}
							}
							
							if (z + winCondition - 1 < board.getDimZ()) {
								for (int i = 0; i < winCondition - 1; i++) {
									if (board.getField(x, y, z + i) == board.getField(x, y, z + i + 1)) {
										if (i + 1 == winCondition -1) {
											return board.getField(x, y, z);
										}
									} else {
										break;
									}
								}
								if (x - winCondition + 1 >= 0) {
									for (int i = 0; i < winCondition - 1; i++) {
										if (board.getField(x - i, y, z + i) == board.getField(x - i - 1, y, z + i + 1)) {
											if (i + 1 == winCondition -1) {
												return board.getField(x, y, z);
											}
										} else {
											break;
										}
									}
									if (y - winCondition + 1 >= 0) {
										for (int i = 0; i < winCondition - 1; i++) {
											if (board.getField(x - i, y - i, z + i) == board.getField(x - i - 1, y - i - 1, z + i + 1)) {
												if (i + 1 == winCondition -1) {
													return board.getField(x, y, z);
												}
											} else {
												break;
											}
										}
									}
								}
								if (y - winCondition + 1 >= 0) {
									for (int i = 0; i < winCondition - 1; i++) {
										if (board.getField(x, y - i, z + i) == board.getField(x, y - i - 1, z + i + 1)) {
											if (i + 1 == winCondition -1) {
												return board.getField(x, y, z);
											}
										} else {
											break;
										}
									}
								}
							}
						}
						
					}
				}
			}
			} catch (OutsidePlayingBoardException e) {
				System.out.println("Winnercheck went outside the playing board");
			}
		return null;
		
	}
	
	public int[] winningMove(Player player) {
		Board boardtemp = board.deepCopy();
		Player[] playertemp = {player};
		Game gametemp = new Game(boardtemp, playertemp, winCondition);
		
		for (int x = 0; x < board.DIMX; x++) {
			for (int y = 0; y < board.DIMY; y++) {
				try {
					boardtemp.setField(x, y, player);
					if (gametemp.checkWinner() == player) {
						int[] xy = {x,y};
						return xy;
					}
				} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
					e.printStackTrace();
				}
			}
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
		Player winner = checkWinner();
		if (winner != null) {
			return true;
		} else {
			return isFull();
		}
	}
	
	public boolean wantRematch() {
		Scanner in = new Scanner(System.in);
		String input = "";
		System.out.println("Do you want a rematch? (y/n) ");
		while (true) {
			input = in.nextLine();
			if (input.equals("y") || input.equals("n")) {
				break;
			} else {
				System.out.println("Please type \"y\" or \"n\".");
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
