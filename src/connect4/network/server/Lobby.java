package connect4.network.server;

import java.util.ArrayList;
import java.util.List;

public class Lobby extends Thread {
	
	public List<ClientHandler> clients;
	public List<ClientHandler> ready;
	public List<ClientHandler> inGame;
	public Server server;
	
	public Lobby(Server server) {
		clients = new ArrayList<ClientHandler>();
		ready = new ArrayList<ClientHandler>();
		this.server = server;
	}
	
	public void addInGame(ClientHandler game) {
		inGame.add(game);
		clients.remove(game);
		ready.remove(game);
	}
	
	public void outGame(ClientHandler client) {
		inGame.remove(client);
		clients.add(client);
	}
	
	public void connect(ClientHandler client) {
		if (!clients.contains(client)) {
			clients.add(client);			
		}

	}
	
	public void ready(ClientHandler client) {
		if (clients.contains(client) && !ready.contains(client)) {
			ready.add(client);				
		}
	}
	
	public void disconnect(ClientHandler client) {
		clients.remove(client);
		ready.remove(client);
		inGame.remove(client);
		client.terminate();
	}
	
	public void startGame() {
		for (int i = 0; i < ready.size(); i++) {
			ClientHandler first = ready.get(i);	
			List<ClientHandler> same = new ArrayList<ClientHandler>();
			same.add(first);
			for (int o = 0; o < ready.size(); o++) {
				ClientHandler other = ready.get(o);
				if (first != other && first.getPlayers() == other.getPlayers() && first.getDimension() == other.getDimension() && first.getNoRoof() == other.getNoRoof() && first.getWinCondition() == other.getWinCondition()) {
					same.add(other);
				}
			}
			if (same.size() == first.getPlayers()) {
				GameHandler game = new GameHandler(same, first.getDimension(), first.getNoRoof(), first.getWinCondition());
				for (ClientHandler client : same) {
					client.setGame(game);
					ready.remove(client);
				}
				game.start();
				break;
			}
		}

	}
	
	public void run() {
		while (true) {
			while (ready.isEmpty() || ready.size() == 1) {
				try {
					Thread.sleep(250);
				} catch (InterruptedException e) {
				}
			}
			int begin = 10;
			int end = 0;
			while (begin != end) {
				begin = ready.size();
				startGame();
				end = ready.size();
			}

		}

	}

}
