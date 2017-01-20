package connect4.game;

import connect4.exceptions.*;

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
	
	public abstract int determineMove(Game game);
	
	public void makeMove(Game game) {
		int choice = determineMove(game);
		if (choice == -1) {
			makeMove(game);
			return;
		} else if (choice == -2) {
				if (game.board.layer < game.board.getDimZ() - 1) {
					game.board.drawLayer(game.board.layer + 1);
				} else {
					System.out.println("You are on the uppermost layer.");
				}
				makeMove(game);
				return;
		} else if (choice == -3) {
				if (game.board.layer > 0) {
					game.board.drawLayer(game.board.layer - 1);
				} else {
					System.out.println("You are on the bottommost layer.");
				}
				makeMove(game);
				return;
		}
		try {
			game.board.setField(choice, this);		
		} catch (OutsidePlayingBoardException e) {
			System.out.println(e.getMessage());
			makeMove(game);
		} catch (NoEmptySpotException e) {
			System.out.println(e.getMessage());
			makeMove(game);
		}

	}
}
