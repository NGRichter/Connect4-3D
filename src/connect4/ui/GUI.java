package connect4.ui;

import connect4.game.GameView;
import connect4.game.Player;
import connect4.network.Buffer;
import connect4.network.Client;

public class Gui extends Thread implements GameView {
	
	private Client client;
	private Buffer buffer;
	
	public Gui() {
		buffer = new Buffer();
	}

	@Override
	public void notifyMove(Player player) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void drawBoard() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void showResult(Player player) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void showError(String message) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setClient(Client client) {
		this.client = client;
		
	}



}
