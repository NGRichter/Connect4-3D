package connected.game;

public class ComputerPlayer extends Player {

	public ComputerPlayer(String name, Colour colour) {
		super(name, colour);

	}

	@Override
	public int determineMove(Board board) {
		return 0;
	}

}
