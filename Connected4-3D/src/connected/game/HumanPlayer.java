package connected.game;

public class HumanPlayer extends Player {

	public HumanPlayer(String name, Colour colour) {
		super(name, colour);
	}

	@Override
	public int determineMove(Board board) {
        String prompt = "> " + getName() + " (" + getColour().name() + ")"
                + ", what is your choice? ";
        return 0;
	}

}
