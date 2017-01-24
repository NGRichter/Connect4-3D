package connect4.network.client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.util.List;

import connect4.game.*;
import connect4.ui.*;

public class Client {

	private Game game = null;
	private Socket sock;
	private ServerHandler server;
	private GameView ui;

	private int boardDim = 4;
	private int winCondition;
	private boolean noRoof;
	private boolean isConnected;
	private boolean inLobby;
	private boolean isReady;
	private boolean inGame;

	
	public static void main(String[] args) {
		if (args.length == 1 && args[0].equals("tui")) {
			GameView tui = new Tui();
			Thread t = new Thread(tui);
			Client client = new Client(tui);
			t.start();
			tui.setClient(client);
		} else if (args.length == 1 && args[0].equals("gui")) {
			GameView gui = new Gui();
			Client client = new Client(gui);
			gui.setClient(client);
		}
	}
	
	public Client(GameView ui) {
		this.ui = ui;
	}

	public GameView getGameView(){
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
	
	public void serverDisconnected() {
		server = null;
	}

	public void setBoardDim(int dim){
		this.boardDim = dim;
	}

	public int getBoardDim(){
		return boardDim;
	}

	public void setWinCondition(int wincondition){
        this.winCondition = wincondition;
    }

    public int getWinCondition(){
        return winCondition;
    }

	public void startClientGame(List<String> usernames) {
		Player[] players = new Player[usernames.size()];
		int i = 0;
		for(String username : usernames){
			players[i] = new HumanPlayer(username, Colour.random());
			i++;
		}
		int boardHeight = boardDim;
		if(noRoof){
			boardHeight = 1000;
		}
		game = new Game(new Board(boardDim, boardDim, boardHeight), players, winCondition);
	}

	public void stopClientGame(){
		game = null;
	}

	public boolean gameIsActive(){
		return game != null;
	}
}
