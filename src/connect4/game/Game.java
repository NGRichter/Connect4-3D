package connect4.game;

import java.util.*;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.ui.Tui;

public class Game extends Observable{
	
	private List<Player> players = new ArrayList<Player>();
	private List<Colour> colours = Colour.allColours();
    private int playerIndex = 0;
 	public Board board;
	private int winCondition;

	/**
	 * Defines a game with a board, players, and win condition.
	 * @param board - board for the game to use
	 * @param players - players that participate in the game
	 * @param win - amount of 'connects' by a player for the game to be won
	 */
	public Game(Board board, Player[] players, int win) {

		for (Player player : players) {
			this.players.add(player);
		}
		this.board = board;
		winCondition = win;
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

	public void makeNextMove(int x, int y) throws NoEmptySpotException, OutsidePlayingBoardException {
        Player nextPlayer = players.get(playerIndex % players.size());
        board.setField(x, y, nextPlayer);
        playerIndex++;
        setChanged();
        notifyObservers(board);
    }


    /**
     * Getter for the wincondition.
     * @return wincondition
     */
	public int getWinCondition(){
        return winCondition;
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
			}
		return null;

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

}

