package connect4.game.AI;

import connect4.game.*;

public interface Strategy {
	
	public int BLOCKCHANCE = 50;
	public int WINCHANCE = 50;
	
	public int determineMove(Game game);
}
