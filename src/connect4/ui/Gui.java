package connect4.ui;

import connect4.game.Board;
import connect4.game.Game;
import connect4.game.GameView;
import connect4.game.Player;
import connect4.network.server.Buffer;
import connect4.network.client.Client;
import javafx.application.Application;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.layout.StackPane;
import javafx.stage.Stage;

import java.io.IOException;
import java.util.Observable;

public class Gui extends Application implements EventHandler<ActionEvent>, GameView {

    private Client client;
    private Game game;

    Button button;

	@Override
	public void start(Stage primaryStage) throws Exception {
        primaryStage.setTitle("Connect4-3D Superior client");

        button = new Button("Connect localhost 27015");
        button.setOnAction(this);

        StackPane layout = new StackPane();
        layout.getChildren().add(button);


        Scene scene = new Scene(layout, 420, 420);
        primaryStage.setScene(scene);
        primaryStage.show();
	}

	@Override
	public void handle(ActionEvent event) {
        if(event.getSource() == button){
            if (client == null){
                showError("No client.");
            }
        }
	}

	@Override
	public void drawBoard() {

	}

	@Override
	public void showMessage(String message) {
        System.out.println(message);
	}

	@Override
	public void showError(String message) {
        System.err.println("ERROR: " + message);
	}

    @Override
    public void writeServer(String command) {
        try {
            client.writeServer(command);
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
            showError("Client changed!");
	}

	@Override
	public void update(Observable o, Object arg) {

	}


    @Override
    public void run() {
        this.launch();
    }
}

