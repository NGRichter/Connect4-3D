package connect4.game;
import connect4.exceptions.*;

import connect4.exceptions.*;

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
				for (int z = 0; z < DIMZ; z++) {
					fields[x][y][z] = null;
				}
			}
		}
	}

	public void setField(int choice, Player player) throws OutsidePlayingBoardException, NoEmptySpotException {
		if (choice >= (DIMX * DIMY) || choice < 0) {
			throw new OutsidePlayingBoardException();
		}
		int[] xyz = index(choice);
		int z = 0;
		while (z < DIMZ && fields[xyz[0]][xyz[1]][z] != null) {
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
		while (z < DIMZ && fields[x][y][z] != null) {
			z += 1;
		}
		if (fields[x][y][z] == null) {
			fields[x][y][z] = player;
		} else {
			throw new NoEmptySpotException();
		}
		
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




    final String operatingSystem = System.getProperty("os.name");

	public void makeLayer(int z) throws OutsidePlayingBoardException {
        String vertFrame = "\n+---+";
        System.out.print("+---+");
        for(int x = 0; x < DIMX; x++){
            vertFrame += "----------+";
            System.out.format(" X %-6d |", x);
        }


        String name = "";
        System.out.println(vertFrame);
        for(int y = 0; y < DIMY; y++){
            System.out.format("Y %-2d|", y);
			for(int x = 0; x < DIMX; x++) {
                if (getField(x, y, z) == null) {
                    name = "";
                } else {
                    name = getField(x, y, z).getName();
                }
                System.out.format(" %-8s |", name);
            }
			System.out.println(vertFrame);
		}
    }

	public int index(int x, int y, int z) throws OutsidePlayingBoardException {
		if (x < 0 || y < 0 || z < 0 || x >= DIMX || y >= DIMY || z >= DIMZ) {
			throw new OutsidePlayingBoardException();
		}
		return x + y * DIMX + z * DIMX * DIMY;
	}

}
