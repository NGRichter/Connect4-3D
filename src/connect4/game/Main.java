package connect4.game;

import connect4.game.AI.*;

public class Main {
	
	public static void main(String[] args) {
		Strategy medium = new Medium();
		Strategy hard = new Hard();
		Player player1 = new ComputerPlayer(args[0], Colour.AERO, medium);
		Player player2 = new ComputerPlayer(args[1], Colour.ACID_GREEN, hard);
		Player[] players = {player1, player2};
		Board board = new Board(6, 6, 6);
		Game game = new Game(board, players, 4);
		game.start();
	}

}
