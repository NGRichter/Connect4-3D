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
	
	public void empty() {
		for (int x = 0; x < DIMX; x++) {
			for (int y = 0; y < DIMY; y++) {
				for (int z = 0; y < DIMZ; z++) {
					fields[x][y][z] = null;
				}
			}
		}
	}

	public void setField(int choice, Player player) throws OutsidePlayingBoardException {
		int[] intarray = index(choice);
		while (fields[intarray[0]][intarray[1]][intarray[2] - 1] == null && intarray[2] > 0) {
			intarray[2] -= 1;
		}
		fields[intarray[0]][intarray[1]][intarray[2]] = player;
		
	}
	
	public void setField(int x, int y, int z, Player player) throws OutsidePlayingBoardException {
		if (x >= DIMX || y >= DIMY || z >= DIMZ || x < 0 || y < 0 || z < 0) {
			throw new OutsidePlayingBoardException();
		}
		while (fields[x][y][z - 1] == null && z > 0) {
			z -= 1;
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
<<<<<<< HEAD


	public String toString{
        String leftAlignFormat = "| %-15s | %-4d |%n";

        System.out.format("+-----------------+------+%n");
        System.out.format("| Column name     | ID   |%n");
        System.out.format("+-----------------+------+%n");
        for (int i = 0; i < 5; i++) {
            System.out.format(leftAlignFormat, "some data" + i, i * i);
        }
        System.out.format("+-----------------+------+%n");
    }
=======
	
	public int index(int x, int y, int z) throws OutsidePlayingBoardException {
		if (x < 0 || y < 0 || z < 0 || x >= DIMX || y >= DIMY || z >= DIMZ) {
			throw new OutsidePlayingBoardException();
		}
		return x + y * DIMX + z * DIMX * DIMY;
	}
	
>>>>>>> origin/master
	
}
