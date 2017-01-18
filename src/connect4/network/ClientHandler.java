package connect4.network;

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
	private ClientBuffer buffer;
	
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
		buffer = new ClientBuffer();
		
	}
	
	public void run() {
		while (true) {
			int tempin;
			String temp = null;
			try {
				while ((tempin = in.read()) != -1) {
					temp += (char) tempin;
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
			buffer.writeBuffer(temp);
			
			
		}
	}
	
	public void handleOutput(String string) throws IOException {
		out.write(string);
		out.flush();
		
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
	
	public ClientBuffer getBuffer() {
		return buffer;
	}
	
	public void makePlayer(String name) {
		if (player == null) {
			this.player = new HumanPlayer(name, Colour.random());
			this.name = name;			
		}

	}

}
