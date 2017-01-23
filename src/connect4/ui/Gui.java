package connect4.ui;

import connect4.game.Board;
import connect4.game.GameView;
import connect4.game.Player;
import connect4.network.server.Buffer;
import connect4.network.client.Client;

import java.util.Observable;

public class Gui extends Thread implements GameView {

	@Override
	public void drawBoard(Board board) {

	}

	@Override
	public void showMessage(String message) {

	}

	@Override
	public void showError(String message) {

	}

	@Override
	public void setClient(Client client) {

	}

	@Override
	public void update(Observable o, Object arg) {

	}
}

