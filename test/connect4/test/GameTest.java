package connect4.test;

import connect4.exceptions.NoEmptySpotException;
import connect4.game.*;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

public class GameTest {

	@Rule public ExpectedException thrown = ExpectedException.none();

	Board board;
	Game game;
	Player player1;
	Player player2;
	Player[] playerarray = new Player[2];
	List<Player> playerList = new ArrayList<>();

	@Before
	public void setUp() throws Exception {
		board = new Board(4, 4, 4);
		player1 = new HumanPlayer("player1", Colour.random());
		player2 = new HumanPlayer("player2", Colour.random());
		playerarray[0] = player1;
		playerarray[1] = player2;
		playerList.add(player1);
		playerList.add(player2);

		game = new Game(board, playerarray, 4);
	}

	@Test
	public void getPlayers() throws Exception {
		assertTrue(game.getPlayers().equals(playerList));
	}

	//Tests if the game resets after calling the method, board should be empty and the current player should be the first
	@Test
	public void reset() throws Exception {
		game.makeNextMove(0, 0);
		game.makeNextMove(1, 1);
		game.reset();
		assertTrue(game.getBoard().isEmpty());
		assertTrue(game.getCurrentPlayer() == player1);
	}

	//Tests if the method return true if the player has won
	@Test
	public void isWinner() throws Exception {
		game.makeNextMove(0, 0);
		game.makeNextMove(1, 1);
		game.makeNextMove(0, 0);
		game.makeNextMove(1, 1);
		game.makeNextMove(0, 0);
		game.makeNextMove(1, 1);
		game.makeNextMove(0, 0);
		//first player should have a height of 4;
		assertTrue(game.isWinner(player1));
		game.reset();
		game.makeNextMove(0, 0);
		game.makeNextMove(1, 1);
		game.makeNextMove(1, 1);
		game.makeNextMove(2, 2);
		game.makeNextMove(3, 3);
		game.makeNextMove(2, 2);
		game.makeNextMove(2, 2);
		game.makeNextMove(3, 3);
		game.makeNextMove(3, 3);
		game.makeNextMove(2, 1);
		game.makeNextMove(3, 3);
		//First player should have the diagonal line 0,0,0 1,1,1 2,2,2 3,3,3;
		assertTrue(game.isWinner(player1));

	}

	//Tests if the makeNextMove method places the right players at the right spots
	@Test
	public void makeNextMove() throws Exception {
		game.makeNextMove(0, 0);
		game.makeNextMove(1, 1);
		game.makeNextMove(1, 1);
		game.makeNextMove(2, 2);
		game.makeNextMove(3, 3);
		assertTrue(game.getBoard().getField(1, 1, 1) == player1);
		assertTrue(game.getBoard().getField(1, 1, 0) == player2);
	}

	//Tests if the method return the player that may make a move
	@Test
	public void getCurrentPlayer() throws Exception {
		assertTrue(game.getCurrentPlayer() == player1);
		game.makeNextMove(0, 0);
		assertTrue(game.getCurrentPlayer() == player2);
		game.makeNextMove(0, 0);
		assertTrue(game.getCurrentPlayer() == player1);
		game.makeNextMove(0, 0);
		assertTrue(game.getCurrentPlayer() == player2);
	}

	//Tests if the checkWinner method returns the player that has won or returns null when no one has won
	@Test
	public void checkWinner() throws Exception {
		game.getBoard().setField(0, 0, player1);
		game.getBoard().setField(0, 0, player1);
		game.getBoard().setField(0, 0, player1);
		game.getBoard().setField(0, 0, player1);
		assertTrue(game.checkWinner() == player1);
		game.getBoard().setFieldToNull(0,0);
		assertFalse(game.checkWinner() == player1);
		assertTrue(game.checkWinner() == null);

	}

	//Tests if the winningMove method returns an int[] with the winning move of a player
	@Test
	public void winningMove() throws Exception {
		game.getBoard().setField(0, 0, player1);
		game.getBoard().setField(1, 1, player1);
		game.getBoard().setField(2, 2, player1);
		int[] xy1 = {3, 3}; //The winning move should be 3, 3
		int[] xy2 = game.winningMove(player1, 4);
		assertTrue(xy1[0] == xy2[0] && xy1[1] == xy2[1]);
	}

	//Tests if the ifFull method returns true if there are no more spaces on the board
	@Test
	public void isFull() throws Exception {
		for (int x = 0; x < game.getBoard().getDimX(); x++) {
			for (int y = 0; y < game.getBoard().getDimY(); y++) {
				for (int z = 0; z < game.getBoard().getDimZ(); z++) {
					assertFalse(game.isFull()); //Check goes before the makeNextMove-method because the last move will make it full, this is checked after the for loops
					game.makeNextMove(x, y);
				}
			}
		}
		assertTrue(game.isFull());
	}

	//Tests if the gameOver method return true if someone has won or the board is full. (Someone said that the board can't be full when playing 1v1 on a 4 dimension board with no winner so I can't that)
	@Test
	public void gameOver() throws Exception {
		game.makeNextMove(0, 0);
		game.makeNextMove(1, 0);
		game.makeNextMove(0, 1);
		game.makeNextMove(1, 1);
		game.makeNextMove(0, 2);
		game.makeNextMove(1, 2);
		assertFalse(game.gameOver());
		game.makeNextMove(0, 3);
		assertTrue(game.gameOver());
	}

	//Tests if an exception is thrown when you try to place your move 5 times on the same spot (height is 4)
	@Test
	public void testNoEmptySpotException() throws Exception {
		thrown.expect(Exception.class);
		thrown.expectMessage("You tried to set your name on a field that is not empty.");
		game.makeNextMove(0, 0);
		game.makeNextMove(0, 0);
		game.makeNextMove(0, 0);
		game.makeNextMove(0, 0);
		game.makeNextMove(0, 0);
	}

	//Tests whether an exception is thrown when you want to place your move outside the scope of the playing board (range [0,3])
	@Test
	public void testOutsidePlayingBoardException() throws Exception {
		thrown.expect(Exception.class);
		thrown.expectMessage("You tried accessing a field outside the range of the board");
		game.makeNextMove(4, 4);

	}

}