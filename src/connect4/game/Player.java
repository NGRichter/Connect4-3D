package connect4.game;

import javafx.scene.paint.Color;

public abstract class Player {

	private final String name;
	private final Color colour;

	public Player(String name, Color colour) {
		this.name = name;
		this.colour = colour;
	}

	public String getName() {
		return name;
	}

	public Color getColour() {
		return colour;
	}

	public String toString() {
		return name;
	}

	public abstract int[] determineMove(Game game, int thinkingtime);

}
