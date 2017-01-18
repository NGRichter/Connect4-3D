package connect4.network;

import java.util.ArrayList;
import java.util.List;

public class Lobby extends Thread {
	
	public List<Client> clients;
	public List<Client> ready;
	
	public Lobby() {
		clients = new ArrayList<Client>();
		ready = new ArrayList<Client>();
	}
	
	public void connect(Client client) {
		clients.add(client);
	}
	
	public void ready(Client client) {
		if (clients.contains(client)) {
			ready.add(client);
		}
	}
	
	public void disconnect(Client client) {
		if (clients.contains(client)) {
			clients.remove(client);
			if (ready.contains(client)) {
				ready.remove(client);
			}
		}
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
