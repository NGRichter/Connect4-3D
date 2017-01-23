package connect4.game;
import java.util.Random;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.AI.*;

public class ComputerPlayer extends Player {
	
	public Strategy strategy;

	public ComputerPlayer(String name, Colour colour, Strategy strategy) {
		super(name, colour);
		this.strategy = strategy;

	}

	@Override
	public int determineMove(Game game) {
		Random random = new Random();		
		int randomchance = random.nextInt(100);
		int[] winner;
		winner = game.winningMove(this, game.getWinCondition());
		if (winner[0] != -1 && randomchance < strategy.getWinChance()) {
			try {
				return game.board.index(winner[0], winner[1], 0);
			} catch (OutsidePlayingBoardException e) {
			}
		}
		for (Player player : game.getPlayers()) {
			if (player != this) {
				winner = game.winningMove(player, game.getWinCondition());
				if (winner[0] != -1 && randomchance < strategy.getBlockChance()) {
					try {
						return game.board.index(winner[0], winner[1], 0);
					} catch (OutsidePlayingBoardException e) {
					}
				}			
			}
			
		}
		return strategy.determineMove(game, this);
	}

}
