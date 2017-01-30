package connect4.network.server;

import connect4.bonus.Challenge;
import connect4.game.HumanPlayer;
import connect4.game.Player;
import javafx.scene.paint.Color;

import java.io.*;
import java.net.Socket;

/**
 * This class represents the clients that are connected to the server.
 */
public class ClientHandler extends Thread {

	private Lobby lobby;
	private Socket sock;
	private BufferedWriter out;
	private BufferedReader in;
	private /*@ spec_public @*/ Player player;
	private /*@ spec_public @*/ String name;
	private boolean isInGame;
	private boolean isInLobby;
	private Buffer buffer;
	private boolean hasChat;
	private boolean hasSecurity;
	private boolean hasLeaderboard;
	private boolean hasChallenge;
	private int amountPlayers;
	private int dimensionOfBoard;
	private boolean noRoof;
	private /*@ spec_public @*/ boolean terminate;
	private GameHandler game;
	private int winCondition;
	private boolean loggedIn;
	private Challenge challengeGame;
	private boolean hasBeenChallenged;

	/**
	 * Makes a new client with all values at their default.
	 * @param lobby - The lobby
	 * @param sock - The socket (connection between server and client)
	 */
	public ClientHandler(Lobby lobby, Socket sock) {
		this.lobby = lobby;
		this.sock = sock;
		try {
			out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
			in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		} catch (IOException e) {
			e.printStackTrace();
		}
		isInGame = false;
		isInLobby = false;
		player = null;
		name = null;
		buffer = new Buffer();
		amountPlayers = 2;
		dimensionOfBoard = 4;
		noRoof = false;
		terminate = false;
		game = null;
		loggedIn = false;
		winCondition = 4;
		challengeGame = null;
		hasBeenChallenged = false;
	}

	/**
	 * Will terminate the thread so it doesn't keep listening.
	 */
	//@ ensures terminate == true;
	public void terminate() {
		terminate = true;
	}

	/**
	 * Will keep listening to incoming messages and store them in the buffer.
	 */
	public void run() {
		while (!terminate) {
			String temp = null;
			try {
				temp = in.readLine();
			} catch (IOException e) {
				terminate = true;
				break;
			}
			buffer.writeBuffer(temp);


		}
	}

	/**
	 * Writes the message given to the client.
	 * @param string - The message you want to send to the client
	 * @throws IOException - If the connection is lost
	 */
	public void handleOutput(String string) throws IOException {
		out.write(string);
		out.newLine();
		out.flush();
	}
/**
 * The below methods are all getters and setter except for the last one.
 * Some methods do not take an argument but set something to true (or false),
 * this is because those values once true should always be true.
 * All getters are //@pure and all setters should have //@ensures variable == true/false/argument.
 */
	public void loggedIn() {
		loggedIn = true;
	}

	public boolean getLoggedIn() {
		return loggedIn;
	}

	public int getWinCondition() {
		return winCondition;
	}

	public void setWinCondition(int win) {
		winCondition = win;
	}

	public GameHandler getGame() {
		return game;
	}

	public void setGame(GameHandler game) {
		this.game = game;
	}

	public int getPlayers() {
		return amountPlayers;
	}

	public void setPlayers(int amount) {
		amountPlayers = amount;
	}

	public int getDimension() {
		return dimensionOfBoard;
	}

	public void setDimension(int dimension) {
		dimensionOfBoard = dimension;
	}

	public boolean getNoRoof() {
		return noRoof;
	}

	public void setNoRoof(boolean noroof) {
		noRoof = noroof;
	}

	public void hasChat() {
		hasChat = true;
	}

	public void hasSecurity() {
		hasSecurity = true;
	}

	public void hasLeaderboard() {
		hasLeaderboard = true;
	}

	public void hasChallenge() {
		hasChallenge = true;
	}

	public boolean getChat() {
		return hasChat;
	}

	public boolean getSecurity() {
		return hasSecurity;
	}

	public boolean getChallenge() {
		return hasChallenge;
	}

	public boolean getLeaderboard() {
		return hasLeaderboard;
	}

	public void inLobby() {
		isInLobby = true;
	}

	public void outLobby() {
		isInLobby = false;
	}

	public void inGame() {
		isInGame = true;
	}

	public void outGame() {
		isInGame = false;
	}

	public BufferedReader getReader() {
		return in;
	}

	public BufferedWriter getWriter() {
		return out;
	}

	public boolean getInGame() {
		return isInGame;
	}

	public boolean getInLobby() {
		return isInLobby;
	}

	public Player getPlayer() {
		return player;
	}

	public String getUserName() {
		return name;
	}

	public Socket getSocket() {
		return sock;
	}

	public Lobby getLobby() {
		return lobby;
	}

	public Buffer getBuffer() {
		return buffer;
	}

	public void setChallengeGame(Challenge challenge) {
		this.challengeGame = challenge;
	}

	public Challenge getChallengeGame() {
		return challengeGame;
	}

	public boolean getHasBeenChallenged() {
		return hasBeenChallenged;
	}

	public void setHasBeenChallenged(boolean hasBeenChallenged) {
		this.hasBeenChallenged = hasBeenChallenged;
	}

	/**
	 * Makes a player to use in games and sets the username to the name.
	 * @param name - The name the clients wants
	 */
	//@ requires name != null;
	//@ ensures this.name == name && player != null;
	public void makePlayer(String name) {
		if (player == null) {
			this.player = new HumanPlayer(name, Color.RED);
			this.name = name;
		}

	}

}
