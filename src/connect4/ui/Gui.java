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
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.PasswordField;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;

import java.io.IOException;
import java.net.InetAddress;
import java.net.URL;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.ResourceBundle;

public class Gui extends Application implements GameView, Initializable {

    private Stage window;
    private Client client;
    private int HEIGHT = 640;
    private int WIDTH = 480;

    @FXML private Button connectButton, joinButton;
    @FXML private TextField ipField, portField, usernameField;
    @FXML private PasswordField passwordField;
    @FXML private HBox connectBox, joinBox;

    @Override
    public void init() {
        client = new Client(this);
    }
    @Override
    public void initialize(URL location, ResourceBundle resources) {
        client = new Client(this);
    }


	@Override
	public void start(Stage primaryStage) throws Exception {
        window = primaryStage;
        window.setTitle("Connect4-3D GUI client");

        Parent main = FXMLLoader.load(getClass().getResource("fxml\\multiplayer.fxml"));

        Scene scene = new Scene(main, HEIGHT, WIDTH);
        primaryStage.setScene(scene);
        primaryStage.show();
	}


	public void connect() {
        try {
            InetAddress address = InetAddress.getByName(ipField.getText());
            int port = Integer.parseInt(portField.getText());
            client.connectServer(port, address);
            writeServer("Join " + usernameField.getText() + " chat security challenge leaderboard");
        } catch (UnknownHostException e) {
            showError("ip-address invalid.");
        } catch (NumberFormatException e) {
            showError("port-number invalid.");
        } catch (IOException e) {
            showError("cannot connect to server");
        }
    }

    public void join() {

        window.setScene(null);
    }

	@Override
    public void run() {
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

	public Client getClient(){
        return client;
    }

    @Override
    public void setClient(Client client) {
        this.client = client;
    }

    @Override
	public void update(Observable o, Object arg) {

	}
}

