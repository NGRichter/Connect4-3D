package connect4.game;

import connect4.exceptions.OutsidePlayingBoardException;

public class Board {
	
	private Player[][][] fields;
	public final int DIMX;
	public final int DIMY;
	public final int DIMZ;
	
	
	public Board(int x, int y, int z) {
		fields = new Player[x][y][z];
		DIMX = x;
		DIMY = y;
		DIMZ = z;
	}

	public void setField(int choice, Player player) throws OutsidePlayingBoardException {
		int[] intarray = index(choice);
		fields[intarray[0]][intarray[1]][intarray[2]] = player;
		
	}
	
	public void setField(int x, int y, int z, Player player) throws OutsidePlayingBoardException {
		if (x >= DIMX || y >= DIMY || z >= DIMZ) {
			throw new OutsidePlayingBoardException();
		}
		fields[x][y][z] = player;
		
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
	
	public Player[][][] getFields() {
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
		if (x >= DIMX || y >= DIMY || z >= DIMZ) {
			throw new OutsidePlayingBoardException();
		}
		player = fields[x][y][z];	
		return player;
	}
	
	public int[] index(int choice) throws OutsidePlayingBoardException {
		int x = choice % DIMX;
		int y = (choice / DIMX) % DIMY;
		int z = choice / (DIMX * DIMY);
		if (z >= DIMZ) {
			throw new OutsidePlayingBoardException();
		}
		int[] array = {x,y,z};
		return array;
		
	}
	
	
}
