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

	public void setField(int choice, Player player) {
		
		
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
	
	public Player getField(int choice) {
		Player player;
		player = fields[x][y][z];
		
		return player;
	}
	
	public int[] index(int choice) throws OutsidePlayingBoardException {
		int x = choice % DIMX;
		int y = (choice / DIMX) % DIMY;
		int z = choice / (DIMX * DIMY);
		if (z > DIMZ) {
			throw new OutsidePlayingBoardException();
		}
		int[] array = {x,y,z};
		return array;
		
	}
	
	
}
