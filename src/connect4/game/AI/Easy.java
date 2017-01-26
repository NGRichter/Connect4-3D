package connect4.game.AI;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Game;
import connect4.game.Player;

import java.util.Random;

public class Easy implements Strategy {

	public int adjacentChance = 75;

	@Override
	public int[] determineMove(Game game, Player player) {
		Random random = new Random();
		int adjacent = random.nextInt(100);
		if (adjacent < adjacentChance) {
			int[] move = adjacent(game, player);
				if (move[0] != -1) {
					return move;
				}
		}
		while (true) {
			int x = random.nextInt(game.board.getDimX());
			int y = random.nextInt(game.board.getDimY());
			int[] xy = {x, y};
			return xy;
		}
	}

	@Override
	public int getWinChance() {
		return 75;
	}

	@Override
	public int getBlockChance() {
		return 75;
	}

	public int[] adjacent(Game game, Player player) {
		int[] adjacent = game.winningMove(player, 2);
		return adjacent;
	}

}
