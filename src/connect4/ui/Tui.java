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

	private Client client;

	@Override
	public void update(Observable observable, Object object) {
		if (observable instanceof Game){
            drawBoard();
			showMessage(object + " has made a move.");
			showMessage("It is the turn of " + ((Game) observable).getCurrentPlayer().getName());
            if (client.getGame().getCurrentPlayer() == client.getAI()) {
                int[] xy = client.getAI().determineMove(client.getGame(), client.getThinkingtime());
                writeServer("Move " + xy[0] + " " + xy[1]);
            }
		}
	}

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
                if (command[0].equals("help")) {
                    showMessage("connect ip-address port-number\r\njoin username\r\nlogin username password\r\nai difficulty-level\r\nready [amount players] [dimension] [noroof (roof)]\r\nmove x y\r\nhint\r\nleave\r\ndisconnect");

                //Connect to a server. 'connect <ip-address> <port>'
                } else if (command[0].equals("connect")) {
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

                //Join the game, with a username. 'join <username>'
                } else if (command[0].equals("join")) {
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

                //Toggle ready for a match by certain rules. 'ready <player amount> <board dimension> <noRoof>'
                } else if (command[0].equals("ready")) {
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

                //Make a move, on coordinates x and y. 'move <x> <y>'
                } else if (command[0].equals("move")) {
                    if (cmdlength == 3) {
                        writeServer("Move " + command[1] + " " + command[2]);
                    } else {
                        showError("incorrect syntax. Use: 'move <X> <Y>'.");
                    }

                //Leave the game and return to the lobby. 'leave'
                } else if (command[0].equals("leave")) {
                    writeServer("Leave");

                //Disconnects from the server. 'disconnect'
                } else if (command[0].equals("disconnect")) {
                    writeServer("Disconnect");
                    client.serverDisconnected();

                //Sends a chatmessage to the server. 'chat <message>'
                } else if (command[0].equals("chat")) {
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

                //Requests the leaderboard from the server.
                } else if (command[0].equals("leaderboard")) {
                    writeServer("Leaderboard");

                //Requests the challenge from the server.
                } else if (command[0].equals("challenge")) {
                    if (cmdlength == 2) {
                        writeServer("Challenge " + command[1]);
                    }

                //Sends a manual command to the server. If you want to test something.
                } else if (command[0].equals("manual")) {
                    String manual = "";
                    for (int i = 1; i < cmdlength; i++) {
                        manual += command[i] + " ";
                    }
                    writeServer(manual);

                } else if (command[0].equals("login")) {
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

                } else if (command[0].equals("ai") && command.length == 2) {
                    try {
                        client.letAIDoGame(true, Integer.parseInt(command[1]));
                        if (Integer.parseInt(command[1]) >= 7) {
                            System.out.println("AI level of 7 or higher can take a long time, please reconsider.");
                        }

                    } catch (NumberFormatException e) {
                        System.out.println("Invalid number.");
                    }

                } else if (command[0].equals("hint")) {
                    writeServer("Hint");

                } else if (command[0].equals("accept")) {
                    writeServer("ChallengeAccept y");

                } else if (command[0].equals("deny")) {
                    writeServer("ChallengeAccept n");

                //If entered command is unknown, offer help.
                } else {
                    showError("Unknown command. Type 'help' for a list of commands.");
                }
            }
        }
    }


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


    @Override
    public void setClient(Client client) {
        this.client = client;
    }

    @Override
    public void gameStarted() {
        //Only for GUI
    }

    @Override
    public void gameOver() {
        //Only for GUI
    }

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

    @Override
    public void showLeaderboard(String leaderboard) {
	    String[] leaderboards = leaderboard.split(" ");
	    String score = "---Leaderboard---";
	    for (int i = 1; i < leaderboards.length; i += 2) {
	        score += "\r\n" + leaderboards[i] + " - " + leaderboards[i + 1];
        }
        showMessage(score);
    }

    @Override
    public void setLogin(boolean success) {
        if (success) {
            showMessage("Login success");
        } else {
            showMessage("Login failure");
        }
    }


    @Override
    public void drawBoard() {
        Board board = client.getGame().getBoard();
        for (int i = 0; i < 5; i++){
            System.out.println("+-------------------------------------------------------------------------+");
        }
        for (int z = (board.getDimZ()-1); z < board.getDimZ() && z >= 0; z--){
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

    @Override
    public void showMessage(String message) {
        System.out.println(message);
    }

    @Override
    public void showChat(String chatmessage) {
        System.out.println(chatmessage);
    }

    @Override
    public void showError(String message) {
        System.err.println("ERROR: " + message);
    }

}
