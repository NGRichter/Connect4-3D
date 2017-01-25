package connect4.game.AI;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Colour;
import connect4.game.Game;
import connect4.game.Player;

public class MinimaxAlpha extends Player {

	public Player player;
	public Player opponent;

	public MinimaxAlpha(String name, Colour colour) {
		super(name, colour);
		player = this;
	}

	@Override
	public int determineMove(Game game) {
		if (game.getPlayers().size() == 2) {
			for (Player players : game.getPlayers()) {
				if (players == this) {
				} else {
					opponent = players;
				}
			}
		}
		return findBestMove(game, 6);
	}

	public int evaluate(Game game) {
		int amount = 0;
		if (game.checkWinner() == player) {
			return 1000;
		} else if (game.checkWinner() == opponent) {
			return -1000;
		}
		int amountplayer = checkIfThreeInARow(game.board, player);
		int amountopponent = checkIfThreeInARow(game.board, opponent);
		amount += amountplayer * 100;
		amount += amountopponent * -100;
		return amount;

	}

	public int checkIfThreeInARow(Board board, Player player) {
		int amount = 0;
		try {
			for (int z = 0; z < board.getDimZ(); z++) {
				for (int y = 0; y < board.getDimY(); y++) {
					for (int x = 0; x < board.getDimX(); x++) {
						if (board.getField(x, y, z) != null) {
							if (x + 4 - 1 < board.getDimX()) {//If there are enough spaces to the right.
								for (int i = 0; i < 3 - 1; i++) {//For every space to the right check if it is the same as the next one.
									if (board.getField(x + i, y, z) == board.getField(x + i + 1, y, z)) {
										if (i + 1 == 3 - 1) {
											if (board.getField(x + i + 2, y, z) == null) {
												amount++;
											}
										}
									} else {
										break;
									}
								}
								if (y + 4 - 1 < board.getDimY()) {
									for (int i = 0; i < 3 - 1; i++) {
										if (board.getField(x + i, y + i, z) == board.getField(x + i + 1, y + i + 1, z)) {
											if (i + 1 == 3 - 1) {
												if (board.getField(x + i + 2, y + i + 2, z) == null) {
													amount++;
												}
											}
										} else {
											break;
										}
									}
								}
								if (z + 4 - 1 < board.getDimZ()) {//If there are enough spaces up also check the diagonal up/right.
									for (int i = 0; i < 3 - 1; i++) {
										if (board.getField(x + i, y, z + i) == board.getField(x + i + 1, y, z + i + 1)) {
											if (i + 1 == 3 - 1) {
												if (board.getField(x + i + 2, y, z + i + 2) == null) {
													amount++;
												}
											}
										} else {
											break;
										}
									}
									if (y + 4 - 1 < board.getDimY()) {//If in all directions there is enough space. (to the right, bottom (y++) and up)
										for (int i = 0; i < 3 - 1; i++) {
											if (board.getField(x + i, y + i, z + i) == board.getField(x + i + 1, y + i + 1, z + i + 1)) {
												if (i + 1 == 3 - 1) {
													if (board.getField(x + i + 2, y + i + 2, z + i + 2) == null) {
														amount++;
													}
												}
											} else {
												break;
											}
										}
									}
									if (y - 4 + 1 >= 0) {//If in all directions there is enough space. (to the right, top (y--) and up)
										for (int i = 0; i < 3 - 1; i++) {
											if (board.getField(x + i, y - i, z + i) == board.getField(x + i + 1, y - i - 1, z + i + 1)) {
												if (i + 1 == 3 - 1) {
													if (board.getField(x + i + 2, y - i - 2, z + i + 2) == null) {
														amount++;
													}
												}
											} else {
												break;
											}
										}
									}

								}

							}


							if (y + 4 - 1 < board.getDimY()) {//If there are enough spaces to the bottom.
								for (int i = 0; i < 3 - 1; i++) {
									if (board.getField(x, y + i, z) == board.getField(x, y + i + 1, z)) {
										if (i + 1 == 3 - 1) {
											if (board.getField(x, y + i + 2, z) == null) {
												amount++;
											}
										}
									} else {
										break;
									}
								}
								if (x - 4 + 1 >= 0) {
									for (int i = 0; i < 3 - 1; i++) {
										if (board.getField(x - i, y + i, z) == board.getField(x - i - 1, y + i + 1, z)) {
											if (i + 1 == 3 - 1) {
												if (board.getField(x - i - 2, y + i + 2, z) == null) {
													amount++;
												}
											}
										} else {
											break;
										}
									}
									if (z + 4 - 1 < board.getDimZ()) {
										for (int i = 0; i < 3 - 1; i++) {
											if (board.getField(x - i, y + i, z + i) == board.getField(x - i - 1, y + i + 1, z + i + 1)) {
												if (i + 1 == 3 - 1) {
													if (board.getField(x - i - 2, y + i + 2, z + i + 2) == null) {
														amount++;
													}
												}
											} else {
												break;
											}
										}
									}
								}
								if (z + 4 - 1 < board.getDimZ()) {
									for (int i = 0; i < 3 - 1; i++) {
										if (board.getField(x, y + i, z + i) == board.getField(x, y + i + 1, z + i + 1)) {
											if (i + 1 == 3 - 1) {
												if (board.getField(x, y + i + 2, z + i + 2) == null) {
													amount++;
												}
											}
										} else {
											break;
										}
									}
								}
							}

							if (z + 4 - 1 < board.getDimZ()) {
								for (int i = 0; i < 3 - 1; i++) {
									if (board.getField(x, y, z + i) == board.getField(x, y, z + i + 1)) {
										if (i + 1 == 3 - 1) {
											if (board.getField(x, y, z + i + 2) == null) {
												amount++;
											}
										}
									} else {
										break;
									}
								}
								if (x - 4 + 1 >= 0) {
									for (int i = 0; i < 3 - 1; i++) {
										if (board.getField(x - i, y, z + i) == board.getField(x - i - 1, y, z + i + 1)) {
											if (i + 1 == 3 - 1) {
												if (board.getField(x - i - 2, y, z + i + 2) == null) {
													amount++;
												}
											}
										} else {
											break;
										}
									}
									if (y - 4 + 1 >= 0) {
										for (int i = 0; i < 3 - 1; i++) {
											if (board.getField(x - i, y - i, z + i) == board.getField(x - i - 1, y - i - 1, z + i + 1)) {
												if (i + 1 == 3 - 1) {
													if (board.getField(x - i - 2, y - i - 2, z + i + 2) == null) {
														amount++;
													}
												}
											} else {
												break;
											}
										}
									}
								}
								if (y - 4 + 1 >= 0) {
									for (int i = 0; i < 3 - 1; i++) {
										if (board.getField(x, y - i, z + i) == board.getField(x, y - i - 1, z + i + 1)) {
											if (i + 1 == 3 - 1) {
												if (board.getField(x, y - i - 2, z + i + 2) == null) {
													amount++;
												}
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
			System.out.println("Winner to see if 3 on a row went outside the playing board");
		}
		return amount;

	}

	public int minimax(int maxDepth, int depth, boolean isMax, Game game, int alpha, int beta) {
		int score = evaluate(game);
		if (score >= 1000) {
			//System.out.println("I returned the max score");
			return score - depth * 30;
		} else if (score <= -1000) {
			//System.out.println("I returned the min score");
			return score + depth * 30;
		}
		if (depth == maxDepth) return score;
		if (isMax) {
			int best = -1000;
			maxouterloop:
			for (int x = 0; x < game.board.getDimX(); x++) {
				for (int y = 0; y < game.board.getDimY(); y++) {
					try {
						if (game.board.getField(x, y, game.board.getDimZ() - 1) == null) {
							game.board.setField(x, y, player);
							best = Math.max(best, minimax(maxDepth, depth + 1, !isMax, game, alpha, beta));
							alpha = Math.max(alpha, best);
							game.board.setFieldToNull(x, y);
							if (beta <= alpha) {
								break maxouterloop;
							}
						}
					} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
						e.printStackTrace();
					}
				}
			}
			return best;
		} else {
			int best = 1000;
			minouterloop:
			for (int x = 0; x < game.board.getDimX(); x++) {
				for (int y = 0; y < game.board.getDimY(); y++) {
					try {
						if (game.board.getField(x, y, game.board.getDimZ() - 1) == null) {
							game.board.setField(x, y, opponent);
							best = Math.min(best, minimax(maxDepth, depth + 1, !isMax, game, alpha, beta));
							beta = Math.min(beta, best);
							game.board.setFieldToNull(x, y);
							if (beta <= alpha) {
								break minouterloop;
							}
						}
					} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
						e.printStackTrace();
					}
				}
			}
			return best;
		}
	}

	public int findBestMove(Game game, int maxDepth) {
		int bestVal = -10000;
		int[] move = new int[2];
		move[0] = -1;
		move[1] = -1;
		for (int x = 0; x < game.board.getDimX(); x++) {
			for (int y = 0; y < game.board.getDimY(); y++) {
				try {
					if (game.board.getField(x, y, game.board.getDimZ() - 1) == null) {
						game.board.setField(x, y, player);
						int moveVal = minimax(maxDepth, 0, false, game, -1000, 1000);
						game.board.setFieldToNull(x, y);
						if (moveVal > bestVal) {
							bestVal = moveVal;
							move[0] = x;
							move[1] = y;
						}
					}
				} catch (OutsidePlayingBoardException | NoEmptySpotException e) {
					e.printStackTrace();
				}
			}
		}
		try {
			if (move[0] != -1) {
				return game.board.index(move[0], move[1], 0);
			}
		} catch (OutsidePlayingBoardException e) {
			e.printStackTrace();
		}
		return -1;
	}
}
