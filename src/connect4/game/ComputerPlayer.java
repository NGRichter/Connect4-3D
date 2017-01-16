package connect4.game;
import connect4.game.AI.*;

public class ComputerPlayer extends Player {
	
	public Strategy strategy;

	public ComputerPlayer(String name, Colour colour, Strategy strategy) {
		super(name, colour);
		this.strategy = strategy;

	}

	@Override
	public int determineMove(Game game) {
		return strategy.determineMove(game);
	}

}
