package connect4.game;

import connect4.exceptions.OutsidePlayingBoardException;

import java.util.Scanner;

public class HumanPlayer extends Player {

	public HumanPlayer(String name, Colour colour) {
		super(name, colour);
	}

	public boolean isInteger(String s) {
		try {
			Integer.parseInt(s);
		} catch (NumberFormatException e) {
			return false;
		} catch (NullPointerException e) {
			return false;
		}
		return true;
	}

	@Override
	public int[] determineMove(Game game) {
		int[] xy = {-1 , -1};
		return xy;
	}

}
