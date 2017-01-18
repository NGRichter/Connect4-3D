package connect4.network;

import java.util.ArrayList;
import java.util.List;

public class Lobby extends Thread {
	
	public List<ClientHandler> clients;
	public List<ClientHandler> ready;
	
	public Lobby() {
		clients = new ArrayList<ClientHandler>();
		ready = new ArrayList<ClientHandler>();
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
		if (clients.contains(client)) {
			clients.remove(client);
			if (ready.contains(client)) {
				ready.remove(client);
			}
		}
		client.terminate();
	}
	
	public void startGame(int playerSize) {
		if (ready.size() >= playerSize) {
			Player[] players;
			for (int i = 0; i < playerSize; i++) {
				players[i] = ready.get(0).getPlayer();
				
			}
		}
	}

}
