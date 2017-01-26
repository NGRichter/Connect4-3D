package connect4.game.AI;

import connect4.game.Game;
import connect4.game.Player;

public interface Strategy {

	public int[] determineMove(Game game, Player player);

	public int getWinChance();

	public int getBlockChance();
}
