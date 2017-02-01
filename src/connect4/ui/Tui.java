package connect4.ui;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Game;
import connect4.game.GameView;
import connect4.game.Player;
import connect4.network.client.Client;

import java.io.Console;
import java.io.IOException;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.Scanner;

public class Tui implements GameView {

	private final String HELP = "help";
	private final String CONNECT = "connect";
	private final String JOIN = "join";
	private final String READY = "ready";
	private final String MOVE = "move";
	private final String LEAVE = "leave";
	private final String DISCONNECT = "disconnect";
	private final String CHAT = "chat";
	private final String LEADERBOARD = "leaderboard";
	private final String CHALLENGE = "challenge";
	private final String MANUAL = "manual";
	private final String LOGIN = "login";
	private final String AI = "ai";
	private final String HINT = "hint";
	private final String ACCEPT = "accept";
	private final String DENY = "deny";
	private Client client;

	/**
	 * After the board is updated it draws the board and checks if the ai
	 * should make a move on the current board.
	 *
	 * @param observable - Game object
	 * @param object     - Name of player who made a move
	 */
	@Override
	public void update(Observable observable, Object object) {
		if (observable instanceof Game) {
			drawBoard();
			showMessage(object + " has made a move.");
			showMessage("It is the turn of " + ((Game) observable).getCurrentPlayer().getName());
			if (client.getGame().getCurrentPlayer() == client.getAI()) {
				int[] xy = client.getAI().determineMove(client.getGame(), client.getThinkingtime());
				writeServer("Move " + xy[0] + " " + xy[1]);
			}
		}
	}

	/**
	 * Waits for input and processes it.
	 */
	public void run() {
		showMessage("Welcome to the Connect4-3D TUI client by Nick & Julian.\r\nType 'help' for a list of commands.");

		Scanner scan = new Scanner(System.in);
		while (true) {
			String[] command = scan.nextLine().split(" ");
			int cmdlength = command.length;
			if (cmdlength >= 1) {

				//Fixes uppercase use in commands.
				command[0] = command[0].toLowerCase();

				//Requests a list of possible commands. 'help'
				if (command[0].equals(HELP)) {
					help();

					//Connect to a server. 'connect <ip-address> <port>'
				} else if (command[0].equals(CONNECT)) {
					connect(command, cmdlength);

					//Join the game, with a username. 'join <username>'
				} else if (command[0].equals(JOIN)) {
					join(command, cmdlength);

					//Toggle ready for a match by certain rules. 'ready <player amount> <board dimension> <noRoof>'
				} else if (command[0].equals(READY)) {
					ready(command, cmdlength);

					//Make a move, on coordinates x and y. 'move <x> <y>'
				} else if (command[0].equals(MOVE)) {
					move(command, cmdlength);

					//Leave the game and return to the lobby. 'leave'
				} else if (command[0].equals(LEAVE)) {
					leave();

					//Disconnects from the server. 'disconnect'
				} else if (command[0].equals(DISCONNECT)) {
					disconnect();

					//Sends a chatmessage to the server. 'chat <message>'
				} else if (command[0].equals(CHAT)) {
					chat(command, cmdlength);

					//Requests the leaderboard from the server.
				} else if (command[0].equals(LEADERBOARD)) {
					leaderboard();

					//Requests the challenge from the server.
				} else if (command[0].equals(CHALLENGE)) {
					challenge(command, cmdlength);

					//Sends a manual command to the server. If you want to test something.
				} else if (command[0].equals(MANUAL)) {
					manual(command, cmdlength);

					//Tries to log into the server or register.
				} else if (command[0].equals(LOGIN)) {
					login(scan);

					//Let the ai play the next game.
				} else if (command[0].equals(AI) && command.length == 2) {
					ai(command[1]);

					//Wants a hint from the server.
				} else if (command[0].equals(HINT)) {
					hint();

					//Accepts the challenge request.
				} else if (command[0].equals(ACCEPT)) {
					accept();

					//Denies the challenge request.
				} else if (command[0].equals(DENY)) {
					deny();

					//If entered command is unknown, offer help.
				} else {
					showError("Unknown command. Type 'help' for a list of commands.");
				}
			}
		}
	}

	/**
	 * Write to server that the client wants to deny the challenge.
	 */
	public void deny() {
		writeServer("ChallengeAccept n");
	}

	/**
	 * Write to server that the client wants to accept the challenge.
	 */
	public void accept() {
		writeServer("ChallengeAccept y");
	}

	/**
	 * Write to server that the client wants a hint.
	 */
	public void hint() {
		writeServer("Hint");
	}

	/**
	 * Let the ai play the next game with a certain difficulty level.
	 *
	 * @param s - Difficulty level
	 */
	public void ai(String s) {
		try {
			client.letAIDoGame(true, Integer.parseInt(s));
			if (Integer.parseInt(s) >= 7) {
				System.out.println("AI level of 7 or higher can take a long time, please reconsider.");
			}

		} catch (NumberFormatException e) {
			System.out.println("Invalid number.");
		}
	}

	/**
	 * Asks for the username and password.
	 * When in an IDE the password is visible, else it is invisible.
	 *
	 * @param scan - Input scanner
	 */
	public void login(Scanner scan) {
		System.out.print("Username: ");
		String username = scan.nextLine();
		Console console = System.console();
		String password;
		//If there is a console use that else just the scanner
		//Console has readPassword which does not echo what you type
		//But this isn't included in Eclipse or Intellij
		if (console != null) {
			password = new String(console.readPassword("Password: "));
			while (password.contains(" ")) {
				showMessage("Password can't contain any spaces");
				password = new String(console.readPassword("Password: "));
			}
		} else {
			System.out.print("Password (it is visible): ");
			password = scan.nextLine();
			for (int i = 0; i < 100; i++) {
				System.out.println("\r\n");
			}
		}
		writeServer("Security " + username + " " + password);
	}

	/**
	 * Writes a manual message to the server.
	 *
	 * @param command   - String[] with your command
	 * @param cmdlength - Length of the string[]
	 */
	public void manual(String[] command, int cmdlength) {
		String manual = "";
		for (int i = 1; i < cmdlength; i++) {
			manual += command[i] + " ";
		}
		writeServer(manual);
	}

	/**
	 * Sends the challenge request to the server.
	 *
	 * @param command   - String[] with your command
	 * @param cmdlength - length of command
	 */
	public void challenge(String[] command, int cmdlength) {
		if (cmdlength == 2) {
			showMessage("Sending challenge request with default parameters");
			writeServer("Challenge 4 2 " + command[1]);
		} else if (cmdlength >= 4 && !command[3].equals("noroof")) {
			try {
				String players = "";
				for (int i = 3; i < cmdlength; i++) {
					players += " " + command[i];
				}
				writeServer("Challenge " + Integer.parseInt(command[1]) + " " + Integer.parseInt(command[2]) + " " + command[3]);
			} catch (NumberFormatException e) {
				showMessage("Invalid numbers");
			}

		} else if (cmdlength >= 5 && command[3].equals("noroof")) {
			try {
				String players = "";
				for (int i = 4; i < cmdlength; i++) {
					players += " " + command[i];
				}
				writeServer("Challenge " + Integer.parseInt(command[1]) + " " + Integer.parseInt(command[2]) + " " + command[3] + players);
			} catch (NumberFormatException e) {
				showMessage("Invalid numbers");
			}
		}
	}

	/**
	 * Requests the leaderboard from the server.
	 */
	public void leaderboard() {
		writeServer("Leaderboard");
	}

	/**
	 * Sends the server a chat message.
	 *
	 * @param command   - String[] with your chat message
	 * @param cmdlength - Length of String[]
	 */
	public void chat(String[] command, int cmdlength) {
		if (cmdlength > 1) {
			String chat = "Chat ";
			for (int i = 1; i < cmdlength; i++) {
				if (i == cmdlength - 1) {
					chat += command[i];
				} else {
					chat += command[i] + " ";
				}
			}
			writeServer(chat);
		}
	}

	/**
	 * Sends the server you want to disconnect.
	 * And disconnect yourself.
	 */
	public void disconnect() {
		writeServer("Disconnect");
		client.serverDisconnected();
	}

	/**
	 * Sends the server you want to leave the game.
	 */
	public void leave() {
		writeServer("Leave");
	}

	/**
	 * Sends the server you want to make a move at a location.
	 *
	 * @param command   - String[] with 2 values
	 * @param cmdlength - Length of String[]
	 */
	public void move(String[] command, int cmdlength) {
		if (cmdlength == 3) {
			writeServer("Move " + command[1] + " " + command[2]);
		} else {
			showError("incorrect syntax. Use: 'move <X> <Y>'.");
		}
	}

	/**
	 * Sends the server you want to start a game with certain parameters.
	 *
	 * @param command   - String[] with parameters
	 * @param cmdlength - Length of String[]
	 */
	public void ready(String[] command, int cmdlength) {
		if (cmdlength == 1) {
			writeServer("Ready");
		} else if (cmdlength == 2) {
			writeServer("Ready " + command[1]);
			client.setBoardDim(4);
			client.setNoRoof(false);
		} else if (cmdlength == 3) {
			writeServer("Ready " + command[1] + " " + command[2]);
			try {
				client.setBoardDim(Integer.parseInt(command[2]));
				client.setNoRoof(false);
			} catch (NumberFormatException e) {
				System.out.println("Invalid number");
			}
		} else if (cmdlength == 4) {
			writeServer("Ready " + command[1] + " " + command[2] + " " + command[3]);
			try {
				client.setBoardDim(Integer.parseInt(command[2]));
				if (command[3].equals("noroof")) {
					client.setNoRoof(true);
				} else {
					client.setNoRoof(false);
				}
			} catch (NumberFormatException e) {
				System.out.println("Invalid number");
			}
		} else {
			showError("incorrect syntax. Use: 'ready' for default match or 'ready <player amount> <board dimension> <noroof>' for custom ruleset.");
		}
	}

	/**
	 * After connecting to the server send this to join lobby.
	 *
	 * @param command   - String[] with parameters
	 * @param cmdlength - Length of String[]
	 */
	public void join(String[] command, int cmdlength) {
		if (cmdlength == 1) {
			showError("incorrect syntax. Use: 'join <username>'.");
		} else if (cmdlength >= 2) {
			if (command[1].length() > 26) {
				showError("username can't exceed 26 characters.");
			} else {
				writeServer("Join " + command[1] + " chat leaderboard security challenge");
				client.setName(command[1]);
			}
		}
	}

	/**
	 * Use this to connect to a server.
	 *
	 * @param command   - String[] with ip address and port number
	 * @param cmdlength - Length of String[]
	 */
	public void connect(String[] command, int cmdlength) {
		if (cmdlength == 3) {
			try {
				int port = Integer.parseInt(command[2]);
				InetAddress address = InetAddress.getByName(command[1]);
				client.connectServer(port, address);
			} catch (UnknownHostException e) {
				showError("ip-address invalid.");
			} catch (NumberFormatException e) {
				showError("port-number invalid.");
			} catch (IOException e) {
				showError("cannot connect to server");
			}
		} else {
			showError("incorrect syntax. Use: 'connect <ip-address> <port>'.");
		}
	}

	/**
	 * Use this command if you don't know what commands you can do.
	 */
	public void help() {
		showMessage("connect ip-address port-number\r\n" +
				"join username\r\n" +
				"login username password\r\n" +
				"ai [difficulty-level]\r\n" +
				"ready [amount players] [dimension] [noroof (roof)]\r\n" +
				"move x y\r\n" +
				"hint\r\n" +
				"challenge [dimension] [amount of players] [noroof] [username] [username2]\r\n" +
				"leave\r\n" +
				"manual [your message]\r\n" +
				"disconnect");
	}


	/**
	 * Writes a message to the server.
	 *
	 * @param string - The message you want to send
	 */
	public void writeServer(String string) {
		try {
			client.writeServer(string);
		} catch (IOException e) {
			showError("no connection to server.");
			client.serverDisconnected();
		} catch (NullPointerException e) {
			showError("no connection to server.");
			e.printStackTrace();
			client.serverDisconnected();
		}
	}


	/**
	 * Sets the client to this.
	 *
	 * @param client - The client you have created
	 */
	@Override
	public void setClient(Client client) {
		this.client = client;
	}

	/**
	 * Draw the board.
	 */
	@Override
	public void gameStarted() {
		drawBoard();
	}

	/**
	 * Does nothing in this class.
	 */
	@Override
	public void gameOver() {
		//Only for GUI
	}

	/**
	 * Show every player you can challenge or every player in the server.
	 *
	 * @param players - String with all players
	 */
	@Override
	public void showPlayers(String players) {
		String[] player = players.split(" ");
		if (player[0].equals("AllPlayers")) {
			String toScreen = "All players in the lobby:";
			for (int i = 1; i < player.length; i++) {
				if (player[i].equals("Game")) {
					toScreen += "\r\nAll players in a game:";
				} else {
					toScreen += "\r\n" + player[i];
				}
			}
			showMessage(toScreen);
		} else if (player[0].equals("Players")) {
			String toScreen = "All players you can challenge:";
			for (int i = 1; i < player.length; i++) {
				toScreen += "\r\n" + player[i];
			}
			showMessage(toScreen);
		}
	}

	/**
	 * Shows you who wants to challenge you.
	 * Or if someone denied the challenge.
	 *
	 * @param challenge - String with challenge information
	 */
	@Override
	public void showChallenge(String challenge) {
		if (challenge.equals("ChallengeDenied")) {
			showMessage("The challenge has been denied by someone.");
		} else {
			String[] challenges = challenge.split(" ");
			if (challenges[3].equals("NoRoof")) {
				System.out.format("Someone wants to challenge you: %s%nDimension: %s%nPlayers: %s%nWith no roof%nSend <Accept> to accept the challenge, <Deny> to deny the challenge.%n", challenges[4], challenges[1], challenges[2]);
			} else {
				System.out.format("Someone wants to challenge you: %s%nDimension: %s%nPlayers: %s%nWith roof%nSend <Accept> to accept the challenge, <Deny> to deny the challenge.%n", challenges[3], challenges[1], challenges[2]);
			}
		}
	}

	/**
	 * Show the leaderboard.
	 *
	 * @param leaderboard - String with usernames and scores
	 */
	@Override
	public void showLeaderboard(String leaderboard) {
		String[] leaderboards = leaderboard.split(" ");
		String score = "---Leaderboard---";
		for (int i = 1; i < leaderboards.length; i += 2) {
			score += "\r\n" + leaderboards[i] + " - " + leaderboards[i + 1];
		}
		showMessage(score);
	}

	/**
	 * Shows success when successfully logged in, or failure if not.
	 *
	 * @param success - boolean if log in succeeded
	 */
	@Override
	public void setLogin(boolean success) {
		if (success) {
			showMessage("Login success");
		} else {
			showMessage("Login failure");
		}
	}

	/**
	 * Draws the current board.
	 */
	@Override
	public void drawBoard() {
		Board board = client.getGame().getBoard();
		for (int i = 0; i < 5; i++) {
			System.out.println("+-------------------------------------------------------------------------+");
		}
		for (int z = (board.getDimZ() - 1); z < board.getDimZ() && z >= 0; z--) {
			System.out.println("Layer: " + z + " out of " + (board.getDimZ() - 1));
			String vertFrame = "\r\n+---+";
			System.out.print("+---+");
			for (int x = 0; x < board.getDimX(); x++) {
				vertFrame += "----------+";
				System.out.format(" X %-6d |", x);
			}
			String name = "";
			System.out.println(vertFrame);
			for (int y = 0; y < board.getDimY(); y++) {
				System.out.format("Y %-2d|", y);
				for (int x = 0; x < board.getDimX(); x++) {
					Player player = null;
					try {
						player = board.getField(x, y, z);
					} catch (OutsidePlayingBoardException e) {
						e.printStackTrace();
					}
					if (player == null) {
						name = "";
					} else {
						name = player.getName();
					}
					System.out.format(" %-8s |", name.substring(0, Math.min(name.length(), 8)));
				}
				System.out.println(vertFrame);
			}
		}
		if (board.isEmpty()) {
			showMessage("It is the turn of " + client.getGame().getCurrentPlayer().getName());
		}
	}

	/**
	 * Shows a message to the ui.
	 *
	 * @param message - Message you want to display
	 */
	@Override
	public void showMessage(String message) {
		System.out.println(message);
	}

	/**
	 * Chat message you get from the server.
	 *
	 * @param chatmessage - Chat message you want to display
	 */
	@Override
	public void showChat(String chatmessage) {
		System.out.println(chatmessage);
	}

	/**
	 * Shows an error message to the ui.
	 *
	 * @param message - Error message you want to display
	 */
	@Override
	public void showError(String message) {
		System.err.println("ERROR: " + message);
	}

}
