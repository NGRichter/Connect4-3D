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
		showMessage("Welcome to the Connect4-3D TUI client by Nick & Julian.\nType 'help' for a list of commands.");
        Scanner scan = new Scanner(System.in);
    	while (true) {
        		String[] command = scan.nextLine().split(" ");
        		if (command.length >= 1) {

                    //Fixes uppercase use in commands.
                    command[0] = command[0].toLowerCase();

                    //Requests a list of possible commands. 'help'
        			if (command[0].equals("help")) {
        				message("connect ip-address port-number\njoin username\nlogin username password\nready [amount players] [dimension] [NoRoof (Roof)] ([win condition])\nmove x y\nleave\ndisconnect");

        			//Connect to a server. 'connect <ip-adress> <port>'
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
        					showError("incorrect syntax. Use: 'connect <ip-address> <port>'.");
        				}

        			//Join the game, with a username. 'join <username>'
        			} else if (command[0].equals("join")) {
        				if (command.length > 2 || command.length == 1) {
        					showError("incorrect syntax. Use: 'join <username>'.");
        				} else {
            				if (command[1].length() > 26) {
            					showError("username can't exceed 26 characters.");
            				} else {
            					writeServer("Join " + command[1]);   						
            				}
        				}

        			//Toggle ready for a match by certain rules. 'ready <player amount> <board dimension> <noRoof>'
                    } else if (command[0].equals("ready")) {
                        if (command.length == 1) {
                            writeServer("Ready");
                        } else if (command.length == 2) {
                            writeServer("Ready " + command[1]);
                        } else if (command.length == 3) {
                            writeServer("Ready " + command[1] + " " + command[2]);
                        } else if (command.length == 4) {
                            writeServer("Ready " + command[1] + " " + command[2] + " " + command[3]);
                        } else {
                            showError("incorrect syntax. Use: 'ready' for default match or 'ready <player amount> <board dimension> <noRoof>' for custom ruleset.");
                        }

                        //Make a move, on coordinates x and y. 'move <x> <y>'
        			} else if (command[0].equals("move")) {
        				if (command.length == 3) {
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
                        if (command.length > 1) {
                            String chat = "Chat ";
                            for (int i = 1; i < command.length; i++) {
                            	if (i == command.length - 1) {
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
        				if (command.length == 2) {
        					writeServer("Challenge " + command[1]);
        				}

        			//Starts a singleplayer game
        			} else if (command[0].equals("singleplayer")) {
        				//TO-DO
        				
        			} else if (command[0].equals("manual")) {
        				String manual = "";
        				for (int i = 1; i < command.length; i++) {
        					manual += command[i] + " ";
        				}
        				writeServer(manual);
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
