package connect4.network.client;

import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Game;
import javafx.scene.paint.Color;

import java.io.*;
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
	private Color colour;

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

			String[] command = receive.split(" ");

			//Starts a game with given playerlist.
			if (command[0].equals("StartGame")) {
				List<String> usernames = new ArrayList<>();
				for (String username : command) {
					if (!username.equals("StartGame")) {
						usernames.add(username);
					}
				}
				client.getGameView().showMessage("Game started with " + usernames);
				client.startClientGame(usernames);
				client.getGameView().gameStarted();
				game = client.getGame();

				//Notifies the client of a move.
			} else if (command[0].equals("NotifyMove")) {
				if (command.length == 3) {
					try {
						game.makeNextMove(Integer.parseInt(command[1]), Integer.parseInt(command[2]));
					} catch (NoEmptySpotException | OutsidePlayingBoardException e) {
						e.printStackTrace();
					}
				}

				//Notify client that game has ended.
			} else if (command[0].equals("GameOver")) {
				if (command[1].equals("Winner") && command.length == 3) {
					client.getGameView().showMessage("The game is over.\r\n" + command[2] + " has won the match!");
				} else {
					client.getGameView().showMessage("The game is over.\r\nIt's a draw!");
				}
				client.getGameView().gameOver();
				client.letAIDoGame(false, 6);

				//Notify client of connection lost.
			} else if (command[0].equals("ConnectionLost")) {
				if (command.length == 2) {
					client.getGameView().showError(receive);
					client.stopClientGame();
				}
				client.letAIDoGame(false, 6);

				//Notify client of an error that occurred.
			} else if (command[0].equals("Error")) {
				String[] disect = receive.split(" ", 2);
				client.getGameView().showError(disect[1]);

			} else if (command[0].equals("Players") || command[0].equals("AllPlayers")) {
				client.getGameView().showPlayers(receive);

			} else if (command[0].equals("ChallengeRequest") || command[0].equals("ChallengeDenied")) {
				client.getGameView().showChallenge(receive);

			} else if (command[0].equals("Leaderboard")) {
				client.getGameView().showLeaderboard(receive);

			} else if (command[0].equals("Security") && command.length == 2) {
				if (command[1].equals("LoginSuccess")) {
					client.getGameView().setLogin(true);
				} else if (command[1].equals("LoginDenied")) {
					client.getGameView().setLogin(false);
				}

				//If not a command, assume chat message & print.
			} else {
				client.getGameView().showMessage(receive);
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
