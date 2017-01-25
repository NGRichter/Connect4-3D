package connect4.bonus;

import connect4.network.server.ClientHandler;
import connect4.network.server.GameHandler;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Challenge extends Thread {

	private Map<ClientHandler, Boolean> clients;
	private int dimension;
	private boolean noRoof;
	private ClientHandler challenger;
	private boolean terminate = false;

	public Challenge(List<ClientHandler> clients, int dimension, boolean noRoof, ClientHandler challenger) {
		System.out.println("Challenge created by " + challenger.getUserName());
		this.clients = new HashMap<>();
		for (ClientHandler client : clients) {
			this.clients.put(client, false);
			client.setChallengeGame(this);
			client.setHasBeenChallenged(true);
			try {
				if (noRoof) {
					client.handleOutput("ChallengeRequest " + dimension + " " + (clients.size() + 1) + " NoRoof " + challenger.getUserName());
				} else {
					client.handleOutput("ChallengeRequest " + dimension + " " + (clients.size() + 1) + " " + challenger.getUserName());
				}
			} catch (IOException e) {
				terminate = true;
				client.getLobby().server.removeClient(client);
			}
		}
		if (terminate) {
			for (ClientHandler client : this.clients.keySet()) {
				try {
					client.handleOutput("ChallengeDenied");
				} catch (IOException e) {

				}
			}
		}
		this.clients.put(challenger, true);
		challenger.setChallengeGame(this);
		challenger.setHasBeenChallenged(true);
		this.dimension = dimension;
		this.noRoof = noRoof;
		this.challenger = challenger;
	}

	public void run() {
		while(!terminate) {
			boolean allReady = true;
			try {
				sleep(250);
			} catch (InterruptedException e) {
			}
			for (ClientHandler client : clients.keySet()) {
				if (!clients.get(client)) {
					allReady = false;
				}
			}
			if (allReady) {
				GameHandler game = new GameHandler(new ArrayList<>(clients.keySet()), dimension, noRoof, 4);
				for (ClientHandler client : clients.keySet()) {
					client.setGame(game);
					client.getLobby().addInGame(client);
					client.setHasBeenChallenged(false);
					client.setChallengeGame(null);
				}
				game.start();
				terminate = true;
			}
		}
	}

	public void acceptChallenge(ClientHandler accept) {
		if (!accept.getInGame()) {
			clients.put(accept, true);
			accept.getLobby().outReady(accept);
			System.out.println("Challenge accepted by " + accept.getUserName());
		}


	}

	public void denyChallenge(ClientHandler denied) {
		System.out.println("Challenge denied by " + denied.getUserName());
		terminate = true;
		for (ClientHandler client : clients.keySet()) {
			client.setHasBeenChallenged(false);
			client.setChallengeGame(null);
			try {
				client.handleOutput("ChallengeDenied");
			} catch (IOException e) {
				client.getLobby().server.removeClient(client);
			}
		}
	}


}
