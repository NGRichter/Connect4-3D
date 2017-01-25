package connect4.game.AI;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Game;
import connect4.game.Player;

import java.util.Random;

public class Medium implements Strategy {

	public int adjacentChance = 90;

	@Override
	public int determineMove(Game game, Player player) {
		Random random = new Random();
		int adjacent2 = random.nextInt(100);
		if (adjacent2 < adjacentChance) {
			int[] move = adjacent2(game, player);
			if (move[0] != -1) {
				try {
					return game.board.index(move[0], move[1], 0);
				} catch (OutsidePlayingBoardException e) {
					e.printStackTrace();
				}
			}
		}
		int adjacent = random.nextInt(100);
		if (adjacent < adjacentChance || adjacent2 < adjacentChance) {
			int[] move2 = adjacent(game, player);
			if (move2[0] != -1) {
				try {
					return game.board.index(move2[0], move2[1], 0);
				} catch (OutsidePlayingBoardException e) {
					e.printStackTrace();
				}
			}
		}
		while (true) {
			int x = random.nextInt(game.board.getDimX());
			int y = random.nextInt(game.board.getDimY());
			try {
				return game.board.index(x, y, 0);
			} catch (OutsidePlayingBoardException e) {
			}
		}
	}

	@Override
	public int getWinChance() {
		return 90;
	}

	@Override
	public int getBlockChance() {
		return 90;
	}

	public int[] adjacent2(Game game, Player player) {
		int[] adjacent = game.winningMove(player, 3);
		return adjacent;
	}

	public int[] adjacent(Game game, Player player) {
		int[] adjacent = game.winningMove(player, 2);
		return adjacent;
	}

}
