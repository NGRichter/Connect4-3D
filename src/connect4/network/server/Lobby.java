package connect4.network.server;

import java.util.ArrayList;
import java.util.List;

public class Lobby extends Thread {

	private List<ClientHandler> clients;
	private List<ClientHandler> ready;
	private List<ClientHandler> inGame;
	public final Server server;

	//@ invariant !clients.contains(null);
	//@ invariant !ready.contains(null);
	//@ invariant !inGame.contains(null);

	public Lobby(Server server) {
		clients = new ArrayList<>();
		ready = new ArrayList<>();
		inGame = new ArrayList<>();
		this.server = server;
	}

	/**
	 * Adds a client to the list of clients that are in game
	 * Removes them from the lobby list and ready list
	 * @param game - the client that starts a game
	 */
	//@ requires game != null;
	//@ ensures inGame.contains(game) && !clients.contains(game) && !ready.contains(game);
	public void addInGame(ClientHandler game) {
		inGame.add(game);
		clients.remove(game);
		ready.remove(game);
	}

	/**
	 * If a client goes out of a game remove them from the game list
	 * and put the client into the lobby list.
	 * @param client - The client that just ended a game
	 */
	//@ requires client != null;
	//@ ensures clients.contains(client) && !inGame.contains(client);
	public void outGame(ClientHandler client) {
		inGame.remove(client);
		clients.add(client);
	}

	/**
	 * If a client is ready to start a game but something happened
	 * and the client has to go out of the ready list.
	 * @param client - The client that has to go out of the ready list
	 */
	//@ requires client != null;
	//@ ensures !ready.contains(client);
	public void outReady(ClientHandler client) {
		ready.remove(client);
	}

	/**
	 * If a client joins the server this command places him in the lobby.
	 * @param client - The client that wants to connect
	 */
	//@ requires client != null;
	//@ ensures clients.contains(client);
	public void connect(ClientHandler client) {
		if (!clients.contains(client)) {
			clients.add(client);
		}
	}

	/**
	 * If a client wants to play a game, put the client into the ready list.
	 * @param client - The client who wants to play a game
	 */
	//@ requires clients.contains(client) && client != null;
	//@ ensures ready.contains(client);
	public void ready(ClientHandler client) {
		if (clients.contains(client)) {
			ready.add(client);
		}
	}

	/**
	 * If a clients disconnects or wants to disconnect
	 * this method will remove the client from the lists.
	 * @param client - The client that disconnects/wants to disconnect
	 */
	//@ requires client != null;
	//@ ensures !clients.contains(client) && !ready.contains(client) && !inGame.contains(client);
	public void disconnect(ClientHandler client) {
		clients.remove(client);
		ready.remove(client);
		inGame.remove(client);
		client.terminate();
	}

	/**
	 * Tries to start a game between clients who are in the ready list.
	 * If no game can be started nothing happens.
	 * If a game can be started a new game will be made on a new thread.
	 * The clients are placed in the inGame list and removed from the other lists.
	 */
	public void startGame() {
		for (int i = 0; i < ready.size(); i++) {
			ClientHandler first = ready.get(i);
			List<ClientHandler> same = new ArrayList<ClientHandler>();
			same.add(first);
			for (int o = 0; o < ready.size(); o++) {
				ClientHandler other = ready.get(o);
				if (first != other &&
						first.getPlayers() == other.getPlayers() &&
						first.getDimension() == other.getDimension() &&
						first.getNoRoof() == other.getNoRoof() &&
						first.getWinCondition() == other.getWinCondition()) {
					same.add(other);
				}
			}
			if (same.size() == first.getPlayers()) {
				GameHandler game = new GameHandler(same, first.getDimension(), first.getNoRoof(), first.getWinCondition());
				for (ClientHandler client : same) {
					client.setGame(game);
					addInGame(client);
				}
				game.start();
				break;
			}
		}

	}
	/**
	 * This thread tries to start games every 1 second.
	 * It sleeps after every time to reduce CPU usage.
	 */
	public void run() {
		while (true) {
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				System.out.println("Lobby has been interrupted");
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
