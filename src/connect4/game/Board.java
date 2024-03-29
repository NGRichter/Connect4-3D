package connect4.game;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;

import java.util.Observable;

public class Board extends Observable {

	private final int DIMX;
	private final int DIMY;
	private final int DIMZ;
	private final Player[][][] fields;


	/**
	 * Defines a board, with a 3D-player array, and X,Y,Z dimensions.
	 *
	 * @param x - x-dimension of the board
	 * @param y - y-dimension of the board
	 * @param z - z-dimension of the board (height)
	 */
	public Board(int x, int y, int z) {
		fields = new Player[x][y][z];
		DIMX = x;
		DIMY = y;
		DIMZ = z;
	}

	/**
	 * Empties the entire board.
	 */
	public void empty() {
		for (int x = 0; x < DIMX; x++) {
			for (int y = 0; y < DIMY; y++) {
				for (int z = 0; z < DIMZ; z++) {
					fields[x][y][z] = null;
				}
			}
		}
	}

	/**
	 * Creates a copy of the board.
	 *
	 * @return copy of board
	 */
	public Board deepCopy() {
		Board board = new Board(DIMX, DIMY, DIMZ);
		for (int z = 0; z < DIMZ; z++) {
			for (int y = 0; y < DIMY; y++) {
				for (int x = 0; x < DIMX; x++) {
					board.fields[x][y][z] = fields[x][y][z];
				}
			}
		}
		return board;
	}

	/**
	 * Sets a field to a player at given coordinates, at it's highest empty field.
	 *
	 * @param x      - x-coordinate of the field
	 * @param y      - y-coordinate of the field
	 * @param player - player to occupy the field with
	 * @throws OutsidePlayingBoardException if x and/or y is outside the board.
	 * @throws NoEmptySpotException if there is no empty spot 
	 * at the highest 'altitude'/'layer'/'slice'/'z-level'.
	 */
	public void setField(int x, int y, Player player) 
			throws OutsidePlayingBoardException, NoEmptySpotException {
		if (x >= DIMX || y >= DIMY || x < 0 || y < 0) {
			throw new OutsidePlayingBoardException();
		}
		int z = 0;
		while (z < DIMZ - 1 && fields[x][y][z] != null) {
			z += 1;
		}
		if (fields[x][y][z] == null) {
			fields[x][y][z] = player;
		} else {
			throw new NoEmptySpotException();
		}

	}


	/**
	 * Sets a field at given coordinates to null, at it's highest non-empty field.
	 *
	 * @param x - x-coordinate of the field
	 * @param y - y-coordinate of the field
	 * @throws OutsidePlayingBoardException if x and/or y is outside the board.
	 */
	public void setFieldToNull(int x, int y) throws OutsidePlayingBoardException {
		if (x >= DIMX || y >= DIMY || x < 0 || y < 0) {
			throw new OutsidePlayingBoardException();
		}
		int z = DIMZ - 1;
		while (z > 0 && fields[x][y][z] == null) {
			z -= 1;
		}
		fields[x][y][z] = null;
	}

	/**
	 * Requests the X-dimension of the board.
	 *
	 * @return DIMX
	 */
	//@ pure
	public int getDimX() {
		return DIMX;
	}

	/**
	 * Requests the Y-dimension of the board.
	 *
	 * @return DIMY
	 */
	//@ pure
	public int getDimY() {
		return DIMY;
	}

	/**
	 * Requests the Z-dimension of the board (height).
	 *
	 * @return DIMZ
	 */
	//@ pure
	public int getDimZ() {
		return DIMZ;
	}

	/**
	 * Requests the 3D-array of players, representing the board.
	 *
	 * @return 3D player array, 'fields'
	 */
	public Player[][][] getFields() {
		return fields;
	}

	/**
	 * Returns current occupation of field, either player or null.
	 *
	 * @param x  - x-coordinate of the field.
	 * @param y  - y-coordinate of the field.
	 * @param z- z-coordinate of the field.
	 * @return player or null if no player.
	 * @throws OutsidePlayingBoardException if x, y and/or z is outside the board.
	 */
	public Player getField(int x, int y, int z) throws OutsidePlayingBoardException {
		Player player;
		if (x >= DIMX || y >= DIMY || z >= DIMZ || x < 0 || y < 0 || z < 0) {
			throw new OutsidePlayingBoardException();
		}
		player = fields[x][y][z];
		return player;
	}

	/**
	 * Return true if board is empty, false if it is not.
	 *
	 * @return true if empty, false if not
	 */
	public boolean isEmpty() {
		for (int z = 0; z < DIMZ; z++) {
			for (int y = 0; y < DIMY; y++) {
				for (int x = 0; x < DIMX; x++) {
					try {
						if (getField(x, y, z) != null) {
							return false;
						}
					} catch (OutsidePlayingBoardException e) {

					}
				}
			}
		}
		return true;
	}

}
