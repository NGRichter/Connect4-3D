package connect4.network;

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
		clients.add(client);
	}
	
	public void ready(ClientHandler client) {
		if (clients.contains(client)) {
			ready.add(client);
		}
	}
	
	public void disconnect(ClientHandler client) {
		clients.remove(client);
		ready.remove(client);
		inGame.remove(client);
		client.terminate();
	}
	
	public void startGame(int playerSize, int dimension, boolean noroof) {
		if (ready.size() >= playerSize) {
			Player[] players;
			for (int i = 0; i < playerSize; i++) {
				players[i] = ready.get(0).getPlayer();
				
			}
		}
	}
	
	public void run() {
		while (true) {
			while (ready.isEmpty()) {
				try {
					Thread.sleep(250);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
			for (ClientHandler client : ready) {
				
			}
		}

	}

}
