package connect4.game;

public class Main {
	
	public static void main(String[] args) {
		Player player1 = new HumanPlayer(args[0], Colour.AERO);
		Player player2 = new HumanPlayer(args[1], Colour.ACID_GREEN);
		Player[] players = {player1, player2};
		Board board = new Board(4, 4, 4);
		Game game = new Game(board, players, 4);
		game.start();
	}

}
