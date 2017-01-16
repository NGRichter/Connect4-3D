package connect4.game.AI;

import java.util.Random;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.*;

public class Easy implements Strategy {
	
	public int BLOCKCHANCE = 50;
	public int WINCHANCE = 50;

	@Override
	public int determineMove(Game game) {
		Random random = new Random();
		int x = random.nextInt(game.board.getDimX());
		int y = random.nextInt(game.board.getDimY());
		try {
			return game.board.index(x, y, 0);
		} catch (OutsidePlayingBoardException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return -1;
	}

}
