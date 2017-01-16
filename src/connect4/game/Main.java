package connect4.game;

public class Main {
	
	public static void main(String[] args) {
		Player player1 = new HumanPlayer(args[0], Colour.AERO);
		Player player2 = new HumanPlayer(args[1], Colour.ACID_GREEN);
		Player player3 = new HumanPlayer("Bassie", Colour.AFRICAN_VIOLET);
		Player[] players = {player1, player2, player3};
		Board board = new Board(6, 6, 999);
		Game game = new Game(board, players, 2);
		game.start();

	}

}
