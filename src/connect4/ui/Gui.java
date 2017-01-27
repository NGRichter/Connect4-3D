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
import javafx.scene.layout.*;
import javafx.stage.Modality;
import javafx.stage.Stage;
import sun.plugin.javascript.navig.Anchor;

import java.io.IOException;
import java.net.InetAddress;
import java.net.URL;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.ResourceBundle;

public class Gui extends Application implements GameView, Initializable {

    private Stage window;
    private Client client;

    //Application settings
    private int HEIGHT = 1280;
    private int WIDTH = 720;
    private boolean RESIZABLE = false;

    @FXML private Button connectButton, joinButton;
    @FXML private TextField ipField, portField, usernameField;
    @FXML private PasswordField passwordField;
    @FXML private HBox connectBox, joinBox;
    @FXML  private Parent root, game;
    private Scene scene;
    @FXML private BorderPane rootPane;

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
        window.setResizable(RESIZABLE);

        FXMLLoader loader = new FXMLLoader(getClass().getResource("fxml\\connect.fxml"));
        loader.setController(this);
        BorderPane mainPane = loader.load();

        scene = new Scene(mainPane);

        primaryStage.setScene(scene);
        primaryStage.show();
}



	public void connect() {
        if (usernameField.getText().trim().isEmpty()){
            showError("Please specify a username.");
        } else try {
            InetAddress address = InetAddress.getByName(ipField.getText());
            int port = Integer.parseInt(portField.getText());
            client.connectServer(port, address);
            writeServer("Join " + usernameField.getText() + " chat security challenge leaderboard");


            FXMLLoader loader = new FXMLLoader(getClass().getResource("fxml\\game.fxml"));
            loader.setController(this);
            try {
                BorderPane gamePane = loader.load();
                scene = new Scene(gamePane);
                window.setScene(scene);
            } catch (IOException e) {
                e.printStackTrace();
            }


        } catch (UnknownHostException e) {
            showError("ip-address invalid.");
        } catch (NumberFormatException e) {
            showError("port-number invalid.");
        } catch (IOException e) {
            showError("cannot connect to server");
        }
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

