package connect4.game.AI;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Colour;
import connect4.game.Game;
import connect4.game.Player;

import java.util.ArrayList;
import java.util.List;

public class MinimaxAlphaV2 extends Player {


	public Player player;
	public Player opponent;

	public MinimaxAlphaV2(String name, Colour colour) {
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
			return 500;
		} else if (game.checkWinner() == opponent) {
			return -500;
		}
		int amountplayerthree = threeInARow(game.board, player);
		int amountopponentthree = threeInARow(game.board, opponent);
		int amountplayertwo = twoInARow(game.board, player);
		int amountopponenttwo = twoInARow(game.board, opponent);
		amount += amountplayerthree * 100;
		amount += amountopponentthree * -100;
		amount += amountplayertwo * 10;
		amount += amountopponenttwo * -10;
		return amount;

	}

	public boolean twoSameTwoNull(List<Player> check, Player player) {
		int players = 0;
		int nulls = 0;
		for (Player threeinarow : check) {
			if (threeinarow == player) {
				players++;
			} else if (threeinarow == null) {
				nulls++;
			} else {
				return false;
			}
		}
		if (players == 2 && nulls == 2) {
			return true;
		} else {
			return false;
		}
	}

	public boolean threeSameOneNull(List<Player> check, Player player) {
		int players = 0;
		int nulls = 0;
		for (Player threeinarow : check) {
			if (threeinarow == player) {
				players++;
			} else if (threeinarow == null) {
				nulls++;
			} else {
				return false;
			}
		}
		if (players == 3 && nulls == 1) {
			return true;
		} else {
			return false;
		}
	}

	public int threeInARow(Board board, Player player) {
		int amount = 0;
		List<Player> temp = new ArrayList<>();
		try {
			for (int z = 0; z < board.getDimZ(); z++) {
				for (int y = 0; y < board.getDimY(); y++) {
					for (int x = 0; x < board.getDimX(); x++) {
						if (x + 3 < board.getDimX()) {
							temp = new ArrayList<>();
							for (int i = 0; i < 3; i++) {
								temp.add(board.getField(x + i, y, z));
							}
							if (threeSameOneNull(temp, player)) {
								amount++;
							}
							if (y + 3 < board.getDimY()) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x + i, y + i, z));
								}
								if (threeSameOneNull(temp, player)) {
									amount++;
								}
							}
							if (z + 3 < board.getDimZ()) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x + i, y, z + i));
								}
								if (threeSameOneNull(temp, player)) {
									amount++;
								}
								if (y + 3 < board.getDimY()) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x + i, y + i, z + i));
									}
									if (threeSameOneNull(temp, player)) {
										amount++;
									}
								}
								if (y - 3 >= 0) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x + i, y - i, z + i));
									}
									if (threeSameOneNull(temp, player)) {
										amount++;
									}
								}

							}

						}


						if (y + 3 < board.getDimY()) {
							temp = new ArrayList<>();
							for (int i = 0; i < 3; i++) {
								temp.add(board.getField(x, y + i, z));
							}
							if (threeSameOneNull(temp, player)) {
								amount++;
							}
							if (x - 3 >= 0) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x - i, y + i, z));
								}
								if (threeSameOneNull(temp, player)) {
									amount++;
								}
								if (z + 3 < board.getDimZ()) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x - i, y + i, z + i));
									}
									if (threeSameOneNull(temp, player)) {
										amount++;
									}
								}
							}
							if (z + 3 < board.getDimZ()) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x, y + i, z + i));
								}
								if (threeSameOneNull(temp, player)) {
									amount++;
								}
							}
						}

						if (z + 3 < board.getDimZ()) {
							temp = new ArrayList<>();
							for (int i = 0; i < 3; i++) {
								temp.add(board.getField(x, y, z + i));
							}
							if (threeSameOneNull(temp, player)) {
								amount++;
							}
							if (x - 3 >= 0) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x - i, y, z + i));
								}
								if (threeSameOneNull(temp, player)) {
									amount++;
								}
								if (y - 3 >= 0) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x - i, y - i, z + i));
									}
									if (threeSameOneNull(temp, player)) {
										amount++;
									}
								}
							}
							if (y - 3 >= 0) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x, y - i, z + i));
								}
								if (threeSameOneNull(temp, player)) {
									amount++;
								}
							}
						}
					}
				}
			}
		} catch (OutsidePlayingBoardException e) {
			e.printStackTrace();
		}

		return amount;
	}

	public int twoInARow(Board board, Player player) {
		int amount = 0;
		List<Player> temp = new ArrayList<>();
		try {
			for (int z = 0; z < board.getDimZ(); z++) {
				for (int y = 0; y < board.getDimY(); y++) {
					for (int x = 0; x < board.getDimX(); x++) {
						if (x + 3 < board.getDimX()) {
							temp = new ArrayList<>();
							for (int i = 0; i < 3; i++) {
								temp.add(board.getField(x + i, y, z));
							}
							if (twoSameTwoNull(temp, player)) {
								amount++;
							}
							if (y + 3 < board.getDimY()) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x + i, y + i, z));
								}
								if (twoSameTwoNull(temp, player)) {
									amount++;
								}
							}
							if (z + 3 < board.getDimZ()) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x + i, y, z + i));
								}
								if (twoSameTwoNull(temp, player)) {
									amount++;
								}
								if (y + 3 < board.getDimY()) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x + i, y + i, z + i));
									}
									if (twoSameTwoNull(temp, player)) {
										amount++;
									}
								}
								if (y - 3 >= 0) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x + i, y - i, z + i));
									}
									if (twoSameTwoNull(temp, player)) {
										amount++;
									}
								}

							}

						}


						if (y + 3 < board.getDimY()) {
							temp = new ArrayList<>();
							for (int i = 0; i < 3; i++) {
								temp.add(board.getField(x, y + i, z));
							}
							if (twoSameTwoNull(temp, player)) {
								amount++;
							}
							if (x - 3 >= 0) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x - i, y + i, z));
								}
								if (twoSameTwoNull(temp, player)) {
									amount++;
								}
								if (z + 3 < board.getDimZ()) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x - i, y + i, z + i));
									}
									if (twoSameTwoNull(temp, player)) {
										amount++;
									}
								}
							}
							if (z + 3 < board.getDimZ()) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x, y + i, z + i));
								}
								if (twoSameTwoNull(temp, player)) {
									amount++;
								}
							}
						}

						if (z + 3 < board.getDimZ()) {
							temp = new ArrayList<>();
							for (int i = 0; i < 3; i++) {
								temp.add(board.getField(x, y, z + i));
							}
							if (twoSameTwoNull(temp, player)) {
								amount++;
							}
							if (x - 3 >= 0) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x - i, y, z + i));
								}
								if (twoSameTwoNull(temp, player)) {
									amount++;
								}
								if (y - 3 >= 0) {
									temp = new ArrayList<>();
									for (int i = 0; i < 3; i++) {
										temp.add(board.getField(x - i, y - i, z + i));
									}
									if (twoSameTwoNull(temp, player)) {
										amount++;
									}
								}
							}
							if (y - 3 >= 0) {
								temp = new ArrayList<>();
								for (int i = 0; i < 3; i++) {
									temp.add(board.getField(x, y - i, z + i));
								}
								if (twoSameTwoNull(temp, player)) {
									amount++;
								}
							}
						}
					}
				}
			}
		} catch (OutsidePlayingBoardException e) {
			e.printStackTrace();
		}

		return amount;
	}

	public int minimax(int maxDepth, int depth, boolean isMax, Game game, int alpha, int beta) {
		int score = evaluate(game);
		if (score == 500) {
			//System.out.println("I returned the max score");
			return score - depth * 30;
		} else if (score == -500) {
			//System.out.println("I returned the min score");
			return score + depth * 30;
		}
		if (depth == maxDepth) return score;
		if (isMax) {
			int best = -500;
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

					}
				}
			}
			return best;
		} else {
			int best = 500;
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

				}
			}
		}
		try {
			if (move[0] != -1) {
				return game.board.index(move[0], move[1], 0);
			}
		} catch (OutsidePlayingBoardException e) {

		}
		return -1;
	}
}