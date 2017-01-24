package connect4.network.client;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class ServerHandler extends Thread {

	private Socket sock;
    private Client client;
	private BufferedReader in;
	private BufferedWriter out;
    private Game game;
	private boolean terminate = false;
    private Colour colour;

    public ServerHandler(Socket sock, Client client) throws IOException {
		this.sock = sock;
        this.client = client;
		in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
    }
	
	public void terminate() {
		terminate = true;
	}
	
	public void run() {
		while (!terminate) {
			String receive = null;
			try {
				receive = in.readLine();
			} catch (IOException e) {
				terminate = true;
				break;
			}
			System.out.println(receive);

			String[] command = receive.split(" ");

            //Starts a game with given playerlist.
            if(command[0].equals("StartGame")) {
                List<String> usernames = new ArrayList<>();
                for (String username : command) {
                    if (!command.equals("StartGame")) {
                        usernames.add(username);
                    }
                }
                client.startClientGame(usernames);

            //Notifies the client of a move.
            } else if(command[0].equals("NotifyMove")){
                if (command.length == 3){
                    try {
                        game.makeNextMove(Integer.parseInt(command[1]), Integer.parseInt(command[2]));
                    } catch (NoEmptySpotException | OutsidePlayingBoardException e) {
                        e.printStackTrace();
                    }
                }

            //Notify client that game has ended.
            } else if(command[0].equals("GameOver")) {
                if(command[1].equals("Winner") && command.length == 3){
                    client.getGameView().showMessage(command[1] + command[2]);
                } else {
                    client.getGameView().showMessage(command[1]);
                }

            //Notify client of connection lost.
            } else if(command[0].equals("ConnectionLost")) {
                if(command.length == 2){
                    client.getGameView().showError(receive);
                    client.stopClientGame();
                }

            //Notify client of an error that occurred.
            } else if(command[0].equals("Error")) {
                client.getGameView().showError(receive);
            }
		}
	}
	
	public void handleOutput(String string) throws IOException {
		out.write(string);
		out.newLine();
		out.flush();
	}
	
	public Socket getSocket() {
		return sock;
	}
	
	public BufferedReader getReader() {
		return in;
	}
	
	public BufferedWriter getWriter() {
		return out;
	}
}
