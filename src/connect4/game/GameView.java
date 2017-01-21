package connect4.game;

import connect4.network.Client;

public interface GameView {

    void run();
    void notifyMove(Player player);
    void drawBoard();
    void showResult(Player player);
    void showError(String message);
    void setClient(Client client);

}
