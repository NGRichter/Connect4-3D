package connect4.game;

import connect4.exceptions.OutsidePlayingBoardException;
import javafx.scene.paint.Color;

import java.util.Scanner;

public class HumanPlayer extends Player {

	public HumanPlayer(String name, Color colour) {
		super(name, colour);
	}

	@Override
	public int[] determineMove(Game game, int thinkingtime) {
		int[] xy = {-1 , -1};
		return xy;
	}

}