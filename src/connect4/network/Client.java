package connect4.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;

import connect4.game.GameView;
import connect4.ui.*;

public class Client {
	
	private Socket sock;
	private ServerHandler server;
	private ClientBuffer buffer;
	private GameView ui;
	
	public static void main(String[] args) {
		if (args.length == 1 && args[0].equals("tui")) {
			GameView tui = new Tui(this);
			Client client = new Client(tui);
		} else if (args.length == 1 && args[0].equals("gui")) {
			GameView gui = new Gui(this);
			Client client = new Client(gui);
		}
	}
	
	public Client(GameView ui) {
		this.ui = ui;
		//ui.start();
	}


	public void connectServer(int port, InetAddress address) throws IOException {
		sock = new Socket(address, port);
		server = new ServerHandler(sock);
		buffer = server.getBuffer();
		server.start();
	}
	
	public void writeServer(String string) throws IOException {
		server.handleOutput(string);
	}
	
	public String readServer() {
		return buffer.readBuffer();
	}
	
}
