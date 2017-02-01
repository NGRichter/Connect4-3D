package connect4.network.client;

import connect4.game.AI.MinimaxHash;
import connect4.game.*;
import connect4.ui.Gui;
import connect4.ui.Tui;
import javafx.application.Application;
import javafx.scene.paint.Color;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class Client {

	private Game game = null;
	private Socket sock;
	private ServerHandler server;
	private GameView ui;
	private Player ai = new MinimaxHash("Me", Color.YELLOW);

	private String name;
	private int boardDim = 4;
	private int winCondition = 4;
	private int thinkingtime;
	private boolean noRoof;
	private boolean aiDoGame;
	private Color[] colors = {Color.DARKBLUE, Color.CYAN, Color.PINK, Color.PURPLE, Color.RED,
		Color.ORANGE, Color.YELLOW, Color.DARKGREEN, Color.LIGHTGREEN, Color.BROWN};
	private List<Color> usedColors = new ArrayList<>();

	public Client(GameView ui) {
		this.ui = ui;
	}

	public static void main(String[] args) {
		if (args.length == 1 && args[0].equals("tui")) {
			GameView tui = new Tui();
			Thread tuiThread = new Thread(tui);
			Client client = new Client(tui);
			tuiThread.start();
			tui.setClient(client);
		} else if (args.length == 1 && args[0].equals("gui")) {
			Application.launch(Gui.class);
		}
	}

	/**
	 * Starts a game on the client, from a list of names.
	 *
	 * @param usernames - usernames of participants for the game.
	 */
	public void startClientGame(List<String> usernames) {
		Player[] players = new Player[usernames.size()];
		int i = 0;
		for (String username : usernames) {
			if (username.equals(name) && aiDoGame) {
				players[i] = ai;
			} else {
				Player newhuman = new HumanPlayer(username, getRandomColor());
				players[i] = newhuman;
			}
			i++;
		}
		int boardHeight = boardDim;
		if (noRoof) {
			boardHeight = 1000;
		}
		game = new Game(new Board(boardDim, boardDim, boardHeight), players, winCondition);
		game.addObserver(ui);
	}


	/**
	 * Requests the GameView.
	 *
	 * @return GameView
	 */
	public GameView getGameView() {
		return ui;
	}


	/**
	 * Connect to a server with a port and InetAdress.
	 *
	 * @param port    - port of the server.
	 * @param address - InetAdress of the server.
	 * @throws IOException
	 */
	public void connectServer(int port, InetAddress address) throws IOException {
		sock = new Socket(address, port);
		server = new ServerHandler(sock, this);
		server.start();
	}

	/**
	 * Sends a command to the server.
	 *
	 * @param string - command to be sent.
	 * @throws IOException
	 */
	public void writeServer(String string) throws IOException {
		if (server != null) {
			server.handleOutput(string);
		} else {
			throw new IOException();
		}

	}

	/**
	 * Requests a random, non-used JavaFX color.
	 *
	 * @return color
	 */
	public Color getRandomColor() {
		int i = (int) (Math.random() * colors.length);
		Color color = colors[i];
		if (!(usedColors.contains(color))) {
			usedColors.add(color);
			return color;
		} else {
			return getRandomColor();
		}
	}

	/**
	 * Let AI play, with specific thinking time.
	 *
	 * @param ai   - let AI play, true or false
	 * @param time - depth level of the AI
	 */
	public void letAIDoGame(boolean ai, int time) {
		aiDoGame = ai;
		thinkingtime = time;
	}

	/**
	 * Requests the thinking time of the AI.
	 *
	 * @return thinking time
	 */
	public int getThinkingtime() {
		return thinkingtime;
	}

	/**
	 * Sets the game to be roofless.
	 *
	 * @param noroof - true or false
	 */
	public void setNoRoof(boolean noroof) {
		noRoof = noroof;
	}

	/**
	 * Disconnects the server by setting it to null.
	 */
	public void serverDisconnected() {
		server = null;
	}


	/**
	 * Sets the dimension of the board.
	 *
	 * @param dim - dimenstion of the board.
	 */
	public void setBoardDim(int dim) {
		boardDim = dim;
	}

	/**
	 * Stops a game on the client, by setting it to null.
	 */
	public void stopClientGame() {
		game = null;
	}

	/**
	 * Requests the game of the client.
	 *
	 * @return game
	 */
	public Game getGame() {
		return game;
	}

	/**
	 * Requests the AI of the client.
	 *
	 * @return AI
	 */
	public Player getAI() {
		return ai;
	}

	/**
	 * Requests the name of the client.
	 *
	 * @return name
	 */
	public String getName() {
		return name;
	}

	/**
	 * Sets the name of the client.
	 *
	 * @param name - string of name to be set.
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * Requeests the server this client is connected to.
	 *
	 * @return server
	 */
	public ServerHandler getServer() {
		return server;
	}
}
