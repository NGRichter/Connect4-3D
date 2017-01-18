package connect4.game;

public interface GameView {

    void start();
    void drawBoard();
    void showResult();
    void showError(String message);

}
