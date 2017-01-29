package connect4.bonus;

import connect4.network.server.ClientHandler;
import connect4.network.server.GameHandler;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Challenge extends Thread {

	private /*@ spec_public @*/ Map<ClientHandler, Boolean> clients;
	private int dimension;
	private boolean noRoof;
	private ClientHandler challenger;
	private boolean terminate = false;

	/**
	 * Makes a new challenge.
	 * Will start a game if all challenged clients accepted.
	 * @param clients - List of clients that are challenged
	 * @param dimension - Dimension of game
	 * @param noRoof - If the game should have a roof
	 * @param challenger - The client that has challenged the others
	 */
	public Challenge(List<ClientHandler> clients, int dimension, boolean noRoof, ClientHandler challenger) {
		System.out.println("Challenge created by " + challenger.getUserName());
		this.clients = new HashMap<>();
		this.clients.put(challenger, true);
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
				denyChallenge(client);
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
		challenger.setChallengeGame(this);
		challenger.setHasBeenChallenged(true);
		this.dimension = dimension;
		this.noRoof = noRoof;
		this.challenger = challenger;
	}

	/**
	 * Will start a game when all participant have accepted.
	 * The thread will sleep for 250 milliseconds between checking to limit cpu usage.
	 */
	public void run() {
		while (!terminate) {
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

	/**
	 * If a client has accepted the challenge this will set a value to true.
	 * @param accept - The client that has accepted
	 */
	//@ requires accept != null;
	//@ ensures clients.get(accept) == true;
	public void acceptChallenge(ClientHandler accept) {
		if (!accept.getInGame()) {
			clients.put(accept, true);
			accept.getLobby().outReady(accept);
			System.out.println("Challenge accepted by " + accept.getUserName());
		}


	}

	/**
	 * If a client has denied the challenge this will send everyone a message saying the challenge has been cancelled.
	 * It will terminate this thread.
	 * @param denied - The client that denied the challenge
	 */
	//@ requires denied != null;
	public void denyChallenge(ClientHandler denied) {
		System.out.println("Challenge denied by " + denied.getUserName());
		terminate = true;
		for (ClientHandler client : clients.keySet()) {
			System.out.format("Sending %s that the challenge has been denied%n", client.getUserName());
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
