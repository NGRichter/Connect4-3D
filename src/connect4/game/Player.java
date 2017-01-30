package connect4.game;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;

public abstract class Player {

	private String name;
	private Colour colour;

	public Player(String name, Colour colour) {
		this.name = name;
		this.colour = colour;
	}

	public String getName() {
		return name;
	}

	public Colour getColour() {
		return colour;
	}

	public String toString() {
		return name + " (" + colour.name() + ")";
	}

	public abstract int[] determineMove(Game game, int thinkingtime);

}
