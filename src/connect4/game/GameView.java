package connect4.game;

import connect4.network.client.Client;

import java.util.Observer;

public interface GameView extends Observer, Runnable {

	void drawBoard();

	void showMessage(String message);

	void showChat(String chatmessage);

	void showError(String error);

	void writeServer(String command);

	void setClient(Client client);

	void gameStarted();

	void gameOver();

	void showPlayers(String players);

	void showChallenge(String challenge);

	void showLeaderboard(String leaderboard);

	void setLogin(boolean success);
}
