package connect4.test;

import connect4.game.Board;
import connect4.game.HumanPlayer;
import connect4.game.Player;
import javafx.scene.paint.Color;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

public class BoardTest {
	Board board;
	Player player;

	@Before
	public void setUp() throws Exception {
		board = new Board(4, 4, 4);
		player = new HumanPlayer("Test", Color.RED);
	}

	//Tests whether the empty method empties the board
	@Test
	public void empty() throws Exception {
		board.setField(0, 0, player);
		board.setField(1, 0, player);
		board.setField(2, 0, player);
		board.setField(3, 0, player);
		assertFalse(board.isEmpty());
		board.empty();
		assertTrue(board.isEmpty());

	}

	//Tests the setField method to see if it sets the player at the correct spots
	@Test
	public void setField() throws Exception {
		board.setField(0, 0, player);
		board.setField(0, 0, player);
		board.setField(0, 0, player);
		assertTrue(board.getField(0, 0, 2) == player);
		board.setField(3, 3, player);
		assertTrue(board.getField(3, 3, 0) == player);
	}

	//Tests if the getField method returns the correct player or null if there is no player
	@Test
	public void getField() throws Exception {
		assertTrue(board.getField(0, 0, 0) == null);
		board.setField(0, 0, player);
		assertTrue(board.getField(0, 0, 0) == player);
	}

	//Tests if the esEmpty method will return true if the board is empty or false if not
	@Test
	public void isEmpty() throws Exception {
		assertTrue(board.isEmpty());
		board.setField(0, 0, player);
		assertFalse(board.isEmpty());
		board.setFieldToNull(0, 0);
		assertTrue(board.isEmpty());
	}

}