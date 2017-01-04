package connected.game;

import java.util.ArrayList;
import java.util.List;

public class Game {
	
	private List<Player> players = new ArrayList<Player>();
	private List<Colour> colours = Colour.allColours();
	
	public Game(Board board, String[] players) {
		int i = 0;
		for (String string : players) {
			Player player = new HumanPlayer(string, colours.get(i));
			this.players.add(player);
			i++;
		}
	}
	
	
}
