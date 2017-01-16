package connect4.game;

import java.util.Scanner;

import connect4.exceptions.OutsidePlayingBoardException;

public class HumanPlayer extends Player {

	public HumanPlayer(String name, Colour colour) {
		super(name, colour);
	}
	
	public boolean isInteger(String s) {
		try { 
	        Integer.parseInt(s); 
	    } catch(NumberFormatException e) { 
	        return false; 
	    } catch(NullPointerException e) {
	        return false;
	    }
		return true;
	}

	@Override
	public int determineMove(Game game) {
        String prompt = "> " + getName() + " (" + getColour().name() + ")"
                + ", what is your choice? (\'X Y, +, -\')";
        System.out.println(prompt);
        Scanner in = new Scanner(System.in);
        String[] input = in.nextLine().split(" ");
		int x = 0, y = 0;  
        try {
        	if (input[0].equals("+")) {
        		return -2;
        	} else if (input[0].equals("-")) {
        		return -3;
        	} else if (isInteger(input[0]) && isInteger(input[1])) {
        		x = Integer.parseInt(input[0]);
        		y = Integer.parseInt(input[1]);
        	} else {
				System.out.println("Invalid input");
				return -1;
			}
        } catch (ArrayIndexOutOfBoundsException e) {
        	System.out.println("Invalid syntax, please try again.");
        	return -1;
        }
        try {
			int choice = game.board.index(x, y, 0);
			return choice;
		} catch (OutsidePlayingBoardException e) {
			System.out.println("Invalid location, please specify a valid x, y and z (\"x y\")");
			return -1;
		}
	}

}
