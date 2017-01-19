package connect4.ui;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Game;
import connect4.game.GameView;
import connect4.game.Player;

import java.util.Scanner;

public class TUI implements GameView {

    private Game game;

    public TUI(Game game){
        this.game = game;
    }

    /*
    Commands:
     - join [username]
     - ready [nr of players (default: 2)] [board dim (default: 4)] [Optional; NoRoof]
     - leave
     - move [x] [y]
     */
    @Override
    public void start() {
        Scanner scan = new Scanner(System.in);
        while(true){
                System.out.println("Enter command (Type 'help' for list of commands)");
                String[] input = scan.nextLine().split(" ");
                if (input.length == 0){
                    showError("No command specified");
                } else if (input[0].equals("join")){
                    //If game hasn't started
                } else if (input[0].equals("ready")){
                    //If game has started
                }
                if (input[0].equals("leave")){

                } else if (input[0].equals("move")){

                }
        }
    }

    @Override
    public void notifyMove(Player player) {
        System.out.println("It's your move, " + player.getName());
    }

    @Override
    public void drawBoard() {
        Board board = game.getBoard();
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
    public void showResult(Player player) {
        if (player != null) {
            System.out.println("MATCH ENDED: Player " + player.getName() + " has won!");
        } else if (player == null){
            System.out.println("MATCH ENDED: It's a draw!");
        }
    }

    @Override
    public void showError(String message) {
        System.out.println("ERROR: " + message);
    }
}
