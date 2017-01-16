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
		return name + "(" + colour.name() + ")";
	}
	
	public abstract int determineMove(Board board);
	
	public void makeMove(Board board) {
		int choice = determineMove(board);
		if (choice == -1) {
			makeMove(board);
			return;
		} else if (choice == -2) {
			if (board.layer < board.getDimZ() - 1) {
                board.drawLayer(board.layer + 1);
            } else {
                System.out.println("You are on the uppermost layer.");
            }
			makeMove(board);
			return;

		} else if (choice == -3) {
			if (board.layer > 0) {
                board.drawLayer(board.layer - 1);
            } else {
                System.out.println("You are on the bottommost layer.");
            }
			makeMove(board);
			return;

		}
		try {
			board.setField(choice, this);		
		} catch (OutsidePlayingBoardException e) {
			System.out.println(e.getMessage());
			makeMove(board);
		} catch (NoEmptySpotException e) {
			System.out.println(e.getMessage());
			makeMove(board);
		}

	}
}
