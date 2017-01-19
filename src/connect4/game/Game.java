package connect4.game;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.ui.TUI;

public class Game {
	
	private List<Player> players = new ArrayList<Player>();
	private List<Colour> colours = Colour.allColours();
	public Board board;
    private GameView gameView;
	private int winCondition;

	/**
	 * Defines a game with a board, players, and win condition.
	 * @param board - board for the game to use
	 * @param players - players that participate in the game
	 * @param win - amount of 'connects' by a player for the game to be won
	 */
	public Game(Board board, Player[] players, int win) {

        gameView = new TUI(this);

		for (Player player : players) {
			this.players.add(player);
		}
		this.board = board;
		winCondition = win;
	}

	/**
	 * Starts the game.
	 */
	public void start() {
		Player winner;
		boolean rematch = true;
		while (rematch) {
			int i = 0;
			while(!gameOver()) {
                players.get(i).makeMove(this);
				i++;
				i = i % players.size();
			}
			winner = checkWinner();
            gameView.showResult(winner);
			rematch = wantRematch();
		}
	}
	
	public List<Player> getPlayers() {
		return players;
	}

	/**
	 * Resets the game by emptying the board.
	 */
	public void reset() {
		board.empty();
	}

	/**
	 * Checks if player has won.
	 * @param player - player to check if won
	 * @return true or false
	 */
	public boolean isWinner(Player player) {
		Player winner = checkWinner();
		if (winner == player) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Getter for the board.
	 * @return board
	 */
	public Board getBoard(){
        return board;
    }

	/**
	 * Checks the board for a winner.
	 * @return winnning player or null
	 */
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

	/**
	 * TO BE REMOVED
	 */
	public int[] winningMove(Player player) {
		Board boardtemp = board.deepCopy();
		Player[] playertemp = {player};
		Game gametemp = new Game(boardtemp, playertemp, winCondition);
		
		for (int x = 0; x < board.getDimX(); x++) {
			for (int y = 0; y < board.getDimY(); y++) {
				try {
					boardtemp.setField(x, y, player);
					if (gametemp.checkWinner() == player) {
						int[] xy = {x,y};
						return xy;
					} else {
						boardtemp.setFieldToNull(x, y);
					}
				} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
					
				}
			}
		}
		int[] noWinningMove = {-1,-1};
		return noWinningMove;
	}

	/**
	 * Checks what next move for player would be the winning move, if any.
	 * @param player - player to check move for
	 * @return coordinates of winning move, -1,-1 if none
	 */
	public int[] winningMove(Player player, int condition) {
		Board boardtemp = board.deepCopy();
		Player[] playertemp = {player};
		Game gametemp = new Game(boardtemp, playertemp, condition);
		
		for (int x = 0; x < board.getDimX(); x++) {
			for (int y = 0; y < board.getDimY(); y++) {
				try {
					boardtemp.setField(x, y, player);
					if (gametemp.checkWinner() == player) {
						int[] xy = {x,y};
						return xy;
					} else {
						boardtemp.setFieldToNull(x, y);
					}
				} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
					
				}
			}
		}
		int[] noWinningMove = {-1,-1};
		return noWinningMove;
	}

	/**
	 * Checks if the board is full.
	 * @return true or false
	 */
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

	/**
	 * Checks if game is over by checking for winner or full board (draw).
	 * @return true or false
	 */
	public boolean gameOver() {
		Player winner = checkWinner();
		if (winner != null) {
			return true;
		} else {
			return isFull();
		}
	}

	/**
	 * TO BE EDITED
	 */
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
