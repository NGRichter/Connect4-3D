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
	private Player AI = new MinimaxHash("Me", Color.YELLOW);

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

	public void startClientGame(List<String> usernames) {
		Player[] players = new Player[usernames.size()];
		int i = 0;
		for (String username : usernames) {
			if (username.equals(name) && aiDoGame) {
				players[i] = AI;
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

	public GameView getGameView() {
		return ui;
	}

	public void connectServer(int port, InetAddress address) throws IOException {
		sock = new Socket(address, port);
		server = new ServerHandler(sock, this);
		server.start();
	}

	public void writeServer(String string) throws IOException {
		if (server != null) {
			server.handleOutput(string);
		} else {
			throw new IOException();
		}

	}

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


	public void letAIDoGame(boolean ai, int time) {
		aiDoGame = ai;
		thinkingtime = time;
	}

	public int getThinkingtime() {
		return thinkingtime;
	}

	public void setNoRoof(boolean noroof) {
		this.noRoof = noroof;
	}

	public void serverDisconnected() {
		server = null;
	}

	public void setBoardDim(int dim) {
		this.boardDim = dim;
	}

	public void stopClientGame() {
		game = null;
	}

	public Game getGame() {
		return game;
	}

	public Player getAI() {
		return AI;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public ServerHandler getServer() {
		return server;
	}
}
