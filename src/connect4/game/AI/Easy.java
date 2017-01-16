package connect4.game.AI;

import java.util.Random;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.*;

public class Easy implements Strategy {
	
	public int adjacentChance = 75;
	
	@Override
	public int determineMove(Game game, Player player) {
		Random random = new Random();
		int adjacent = random.nextInt(100);
		if (adjacent < adjacentChance) {
			int[] move = adjacent(game, player);
			try {
				if (move[0] != -1) {
					return game.board.index(move[0], move[1], 0);					
				}
			} catch (OutsidePlayingBoardException e) {
				e.printStackTrace();
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
