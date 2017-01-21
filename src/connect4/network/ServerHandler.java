package connect4.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

public class ServerHandler extends Thread {

	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private boolean terminate = false;
	private ClientBuffer buffer;
	
	public ServerHandler(Socket sock) throws IOException {
		this.sock = sock;
		in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		buffer = new ClientBuffer();
	}
	
	public void terminate() {
		terminate = true;
	}
	
	public void run() {
		while (!terminate) {
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
	
	public Socket getSocket() {
		return sock;
	}
	
	public ClientBuffer getBuffer(){
		return buffer;
	}
	
	public BufferedReader getReader() {
		return in;
	}
	
	public BufferedWriter getWriter() {
		return out;
	}
}
