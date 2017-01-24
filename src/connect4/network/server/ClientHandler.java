package connect4.network.server;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

import connect4.game.*;

public class ClientHandler extends Thread {
	
	private Lobby lobby;
	private Socket sock;
	private BufferedWriter out;
	private BufferedReader in;
	private Player player;
	private String name;
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
	private boolean terminate;
	private GameHandler game;
	private int winCondition;
	private boolean loggedIn;
	
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
	}
	
	public void terminate() {
		terminate = true;
	}
	
	public void run() {
		while (!terminate) {
			String temp = null;
			try {
				temp = in.readLine();
			} catch (IOException e) {
				e.printStackTrace();
				terminate = true;
				break;
			}
			buffer.writeBuffer(temp);
			
			
		}
	}
	
	public void handleOutput(String string) throws IOException {
		out.write(string);
		out.newLine();
		out.flush();
	}
	
	public void setGame(GameHandler game) {
		this.game = game;
	}
	
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
	
	public void setPlayers(int amount) {
		amountPlayers = amount;
	}
	
	public void setDimension(int dimension) {
		dimensionOfBoard = dimension;
	}
	
	public void setNoRoof(boolean noroof) {
		noRoof = noroof;
	}
	
	public int getPlayers() {
		return amountPlayers;
	}
	
	public int getDimension() {
		return dimensionOfBoard;
	}
	
	public boolean getNoRoof() {
		return noRoof;
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
	
	public void makePlayer(String name) {
		if (player == null) {
			this.player = new HumanPlayer(name, Colour.random());
			this.name = name;			
		}

	}

}
