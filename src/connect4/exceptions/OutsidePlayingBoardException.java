package connect4.exceptions;

public class OutsidePlayingBoardException extends Exception {

	public String getMessage() {
		return "You tried accessing a field outside the range of the board";
	}

}
