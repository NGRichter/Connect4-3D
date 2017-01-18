package connect4.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

public class ClientHandler extends Thread {
	
	private Lobby lobby;
	private Socket sock;
	private BufferedWriter out;
	private BufferedReader in;
	
	public ClientHandler(Lobby lobby, Socket sock) {
		this.lobby = lobby;
		this.sock = sock;
		try {
			out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
			in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
	
	public void run() {
		
	}
	
	public void handleOutput() {
		
	}

}
