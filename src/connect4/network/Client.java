package connect4.network;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;

import connect4.game.GameView;
import connect4.ui.*;

public class Client {
	
	private Socket sock;
	private ServerHandler server;
	private Buffer buffer;
	private GameView ui;
	
	public static void main(String[] args) {
		if (args.length == 1 && args[0].equals("tui")) {
			GameView tui = new Tui();
			Client client = new Client(tui);
			tui.setClient(client);
		} else if (args.length == 1 && args[0].equals("gui")) {
			GameView gui = new Gui();
			Client client = new Client(gui);
			gui.setClient(client);
		}
	}
	
	public Client(GameView ui) {
		this.ui = ui;
		//ui.start();
	}
	
	public Buffer getBuffer() {
		return buffer;
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
	
	public void serverDisconnected() {
		server = null;
	}
	
}
