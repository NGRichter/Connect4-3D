package connect4.ui;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Game;
import connect4.game.GameView;
import connect4.game.Player;
import connect4.network.client.Client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.Scanner;

public class Tui implements GameView {

	private Client client;
    private Game game;

    public Tui(){

    }


	@Override
	public void update(Observable observable, Object arg) {
		if (observable instanceof Game){
			drawBoard((Board) arg);
		}
	}


    public void setClient(Client client) {
    	this.client = client;
    }

    /*
    Commands:
     - singleplayer
     - connect ip-address port-number
     - join username
     - login username password
     - ready [nr of players (default: 2)] [board dim (default: 4)] [NoRoof (Roof)] (Roof is not in the protocol but only in our implementation) so is -> [win condition (default: 4)]
     - leave
     - move [x] [y]
     - leaderboard
     - challenge username
     - chat [message]
     */
    
    public void run() {
        Scanner scan = new Scanner(System.in);
    	while (true) {
        		String[] command = scan.nextLine().split(" ");
        		if (command.length >= 1) {

                    //Requests a list of possible commands.
        			if (command[0].equals("help")) {
        				message("connect ip-address port-number\njoin username\nlogin username password\nready [amount players] [dimension] [NoRoof (Roof)] ([win condition])\nmove x y\nleave\ndisconnect");

        			//Connect to a server.
        			} else if (command[0].equals("connect")) {
        				if (command.length == 3) {
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
        					showError("please specify an ip-address and a port-number");
        				}

        			//Join the game, with a username.
        			} else if (command[0].equals("join") && command.length >= 2) {
        				if (command.length > 2) {
        					showError("join only wants your username, please do not use spaces");
        				} else {
            				if (command[1].length() > 26) {
            					showError("username can't be more than 26 characters");
            				} else {
            					writeServer("Join " + command[1]);   						
            				}
        				}

        			//Make a move, on coordinates x and y.
        			} else if (command[0].equals("move")) {
        				if (command.length == 3) {
        					writeServer("Move " + command[1] + command[2]);	
        				} else {
        					showError("\"move X Y\"");
        				}

        			//Leave the game and return to the lobby.
        			} else if (command[0].equals("leave")) {
        				writeServer("Leave");

                    //Disconnects from the server.
        			} else if (command[0].equals("disconnect")) {
        				writeServer("Disconnect");
    					client.serverDisconnected();

                    //Sends a chatmessage to the server.
        			} else if (command[0].equals("chat")) {
        				String chat = "Chat ";
        				for (int i = 1; i < command.length; i++) {
        					chat += command[i];
        				}
        				writeServer(chat);

                    //Requests the leaderboard from the server.
        			} else if (command[0].equals("leaderboard")) {
        				writeServer("Leaderboard");

                    //Requests the challenge from the server.
        			} else if (command[0].equals("challenge")) {
        				if (command.length == 2) {
        					writeServer("Challenge " + command[1]);
        				}
        			} else if (command[0].equals("singleplayer")) {
        				//TO-DO
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

    public void message(String message) {
    	System.out.println(message);
    }

    @Override
    public void drawBoard(Board board) {
        for (int z = board.getDimZ(); z >= 0; z--){
            System.out.println("Layer: " + z + " out of " + (board.getDimZ()-1));
            String vertFrame = "\n+---+";
            System.out.print("+---+");
            for(int x = 0; x < board.getDimX(); x++){
                vertFrame += "----------+";
                System.out.format(" X %-6d |", x);
            }
            String name = "";
            System.out.println(vertFrame);
            for(int y = 0; y < board.getDimY(); y++){
                System.out.format("Y %-2d|", y);
                for(int x = 0; x < board.getDimX(); x++) {
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
    }

    @Override
    public void showMessage(String message) {
        System.out.println(message);
    }

    @Override
    public void showError(String message) {
        System.err.println("ERROR: " + message);
    }

}
