package connect4.exceptions;

public class NoEmptySpotException extends Exception {

	public String getMessage() {
		return "You tried to set your name on a field that is not empty.";
	}
	
}
