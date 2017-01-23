package connect4.game;

import connect4.network.client.Client;

import java.util.Observer;

public interface GameView  extends Observer, Runnable {

    void drawBoard(Board board);
    void showMessage(String message);
    void showError(String message);
    void setClient(Client client);

}
