package connect4.game.AI;

import connect4.game.Game;
import connect4.game.Player;

public interface Strategy {

	int[] determineMove(Game game, Player player);

	int getWinChance();

	int getBlockChance();
}
