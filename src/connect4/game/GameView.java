package connect4.game;

import connect4.network.client.Client;

import java.util.Observer;

public interface GameView  extends Observer, Runnable {

    void drawBoard();
    void showMessage(String message);
    void showError(String error);
    void writeServer(String command);
    void setClient(Client client);

}
