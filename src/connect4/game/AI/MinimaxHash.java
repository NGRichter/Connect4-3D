package connect4.game.AI;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Colour;
import connect4.game.Game;
import connect4.game.Player;

import java.util.*;

public class MinimaxHash extends Player {

	public Player player;
	public Player opponent;
	private long[][][][] hashTable = new long[4][4][4][3];
	private Map<Long, Integer> hashMap;
	private Random random = new Random();

	public MinimaxHash(String name, Colour colour) {
		super(name, colour);
		player = this;
		initTable();
		hashMap = new HashMap<>();
	}

	public long randomNumber() {
		return random.nextLong();
	}

	public int indexOfPlayer(Player player) {
		if (player == this.player) {
			return 0;
		} else if (player == this.opponent) {
			return 1;
		} else if (player == null) {
			return 2;
		}
		return -1;
	}

	public void initTable() {
		for (int z = 0; z < 4; z++) {
			for (int y = 0; y < 4; y++) {
				for (int x = 0; x < 4; x++) {
					for (int p = 0; p < 3; p++) {
						hashTable[z][y][x][p] = randomNumber();
					}
				}
			}
		}
	}

	public long computeHash(Board board) {
		long h = 0;
		for (int z = 0; z < 4; z++) {
			for (int y = 0; y < 4; y++) {
				for (int x = 0; x < 4; x++) {
					if (board.getFields()[z][y][x] !=  null) {
						h ^= hashTable[z][y][x][indexOfPlayer(board.getFields()[z][y][x])];
					}
				}
			}
		}
		return h;
	}

	@Override
	public int[] determineMove(Game game) {
		if (game.getPlayers().size() == 2) {
			for (Player players : game.getPlayers()) {
				if (players == this) {
				} else {
					opponent = players;
				}
			}
		}
		return findBestMove(game, 7);
	}

	public int evaluate(Game game) {
		long h = 0;
		if (hashMap.containsKey(h = computeHash(game.getBoard()))) {
			return hashMap.get(h);
		}
		int amount = 0;
		if (game.checkWinner() == player) {
			hashMap.put(computeHash(game.getBoard()) , 1000);
			return 1000;
		} else if (game.checkWinner() == opponent) {
			hashMap.put(computeHash(game.getBoard()) , -1000);
			return -1000;
		}
		int amountplayer = threeInARow(game.board, player);
		int amountopponent = threeInARow(game.board, opponent);
		amount += amountplayer * 100;
		amount += amountopponent * -100;
		hashMap.put(computeHash(game.getBoard()) , amount);
		return amount;

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

	public int[] findBestMove(Game game, int maxDepth) {
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
		return move;
	}
}
