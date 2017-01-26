package connect4.game;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.AI.Strategy;

import java.util.Random;

public class ComputerPlayer extends Player {

	public Strategy strategy;

	/**
	 * Makes a computerplayer that will play using a given strategy.
	 * @param name - Name of the computerplayer
	 * @param colour - The colour of the computerplayer
	 * @param strategy - The strategy of the computerplayer
	 */

	public ComputerPlayer(String name, Colour colour, Strategy strategy) {
		super(name, colour);
		this.strategy = strategy;

	}

	/**
	 * Determines the index of the place the computerplayer wants to play.
	 * @param game - The game in which the computer player plays
	 * @return index at which the computerplayer wants to play
	 */
	@Override
	public int[] determineMove(Game game) {
		Random random = new Random();
		int randomchance = random.nextInt(100);
		int[] winner;
		winner = game.winningMove(this, game.getWinCondition());
		if (winner[0] != -1 && randomchance < strategy.getWinChance()) {
			return winner;
		}
		for (Player player : game.getPlayers()) {
			if (player != this) {
				winner = game.winningMove(player, game.getWinCondition());
				if (winner[0] != -1 && randomchance < strategy.getBlockChance()) {
					return winner;
				}
			}

		}
		return strategy.determineMove(game, this);
	}

}
