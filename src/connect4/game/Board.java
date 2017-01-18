package connect4.game;
import connect4.exceptions.*;

public class Board {

	private Player[][][] fields;
	private final int DIMX;
	private final int DIMY;
	private final int DIMZ;
	public int layer;


	public Board(int x, int y, int z) {
		fields = new Player[x][y][z];
		DIMX = x;
		DIMY = y;
		DIMZ = z;
		layer = 0;
	}

	public void empty() {
		for (int x = 0; x < DIMX; x++) {
			for (int y = 0; y < DIMY; y++) {
				for (int z = 0; z < DIMZ; z++) {
					fields[x][y][z] = null;
				}
			}
		}
	}
	
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

	public void setField(int choice, Player player) throws OutsidePlayingBoardException, NoEmptySpotException {
		if (choice >= (DIMX * DIMY * DIMZ) || choice < 0) {
			throw new OutsidePlayingBoardException();
		}
		int[] xyz = index(choice);
		int z = 0;
		while (z < DIMZ - 1 && fields[xyz[0]][xyz[1]][z] != null) {
			z += 1;
		}
		if (fields[xyz[0]][xyz[1]][z] == null) {
			fields[xyz[0]][xyz[1]][z] = player;
		} else {
			throw new NoEmptySpotException();
		}
	}

	public void setField(int x, int y, Player player) throws OutsidePlayingBoardException, NoEmptySpotException {
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

	public int getDimX() {
		return DIMX;
	}

	public int getDimY() {
		return DIMY;
	}

	public int getDimZ() {
		return DIMZ;
	}

	public int getLayer() {
		return layer;
	}

	public Player[][][] getFields()	{
		return fields;
	}

	public Player getField(int choice) throws OutsidePlayingBoardException {
		Player player;
		int[] intarray;
		intarray = index(choice);
		player = fields[intarray[0]][intarray[1]][intarray[2]];

		return player;
	}

	public Player getField(int x, int y, int z) throws OutsidePlayingBoardException {
		Player player;
		if (x >= DIMX || y >= DIMY || z >= DIMZ || x < 0 || y < 0 || z < 0) {
			throw new OutsidePlayingBoardException();
		}
		player = fields[x][y][z];
		return player;
	}

	public int[] index(int choice) throws OutsidePlayingBoardException {
		if ((choice < 0) || (choice >= DIMX * DIMY * DIMZ)) {
			throw new OutsidePlayingBoardException();
		}
		int x = choice % DIMX;
		int y = (choice / DIMX) % DIMY;
		int z = choice / (DIMX * DIMY);
		int[] array = {x,y,z};
		return array;

	}


	public int index(int x, int y, int z) throws OutsidePlayingBoardException {
		if (x < 0 || y < 0 || z < 0 || x >= DIMX || y >= DIMY || z >= DIMZ) {
			throw new OutsidePlayingBoardException();
		}
		return x + y * DIMX + z * DIMX * DIMY;
	}

}
