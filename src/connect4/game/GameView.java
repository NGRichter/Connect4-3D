package connect4.game;

public interface GameView {

    void start();
    void notifyMove(Player player);
    void drawBoard();
    void showResult(Player player);
    void showError(String message);

}
