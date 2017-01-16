package connect4.game;

import java.util.Scanner;

import connect4.exceptions.OutsidePlayingBoardException;

public class HumanPlayer extends Player {

	public HumanPlayer(String name, Colour colour) {
		super(name, colour);
	}

	@Override
	public int determineMove(Board board) {
        String prompt = "> " + getName() + " (" + getColour().name() + ")"
                + ", what is your choice? (\"x y\")";
        System.out.println(prompt);
        Scanner in = new Scanner(System.in);
        String[] input = in.nextLine().split(" ");
        int x, y;
        try {
        	x = Integer.parseInt(input[0]);
        	y = Integer.parseInt(input[1]);
        } catch (ArrayIndexOutOfBoundsException e) {
        	System.out.println("Invalid syntax, please try again.");
        	return -1;
        }
        try {
			int choice = board.index(x, y, 0);
			return choice;
		} catch (OutsidePlayingBoardException e) {
			System.out.println("Invalid location, please specify a valid x, y and z (\"x y\")");
			return -1;
		}
	}

}
