package connect4.ui;

import connect4.game.Board;
import connect4.game.Game;
import connect4.game.GameView;
import connect4.game.Player;
import connect4.network.server.Buffer;
import connect4.network.client.Client;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.stage.Modality;
import javafx.stage.Stage;
import sun.font.FontManagerNativeLibrary;
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

    private Scene scene;
    @FXML private Button connectButton, joinButton, moveButton, readyButton;
    @FXML private TextField ipField, portField, usernameField, chatField, xField,
            yField, boardDimField, playerAmountField;
    @FXML private TextArea messageArea;
    @FXML private Label errorField, readyInfo;
    @FXML private RadioButton noRoofButton;
    @FXML private PasswordField passwordField;
    @FXML private HBox connectBox, joinBox, lobbyTools, gameTools;
    @FXML private VBox readyBox;
    @FXML private Parent root, game;
    @FXML private BorderPane gamePane;
    @FXML private Pane connectPane, lobbyPane;

    @Override
    public void init() {
        client = new Client(this);
    }

    @Override
    public void initialize(URL location, ResourceBundle resources) {
        client = new Client(this);
        //Initialize the stackpane setup.
        gamePane.setVisible(false);
        gamePane.toBack();
        connectPane.setVisible(true);
        connectPane.toFront();
    }


	@Override
	public void start(Stage primaryStage) throws Exception {
        window = primaryStage;
        window.setTitle("Connect4-3D GUI client");
        window.setResizable(RESIZABLE);

        root = FXMLLoader.load(getClass().getResource("fxml\\stackedUI.fxml"));
        Platform.setImplicitExit(false);
        scene = new Scene(root);

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

            connectPane.toBack();
            connectPane.setVisible(false);
            gamePane.toFront();
            gamePane.setVisible(true);
        } catch (UnknownHostException e) {
            showError("ip-address invalid.");
        } catch (NumberFormatException e) {
            showError("port-number invalid.");
        } catch (IOException e) {
            showError("cannot connect to server");
        }
    }

    public void setReady(){
        int playerAmount = 2;
        int boardDim = 4;
        String noRoof = "";
        if (!(playerAmountField.getText().trim().isEmpty())) {
            playerAmount = Integer.parseInt(playerAmountField.getText());
        }
        if (!(boardDimField.getText().trim().isEmpty())){
            boardDim = Integer.parseInt(boardDimField.getText());
        }
        writeServer("Ready " + playerAmount + " " + boardDim + " " + noRoof);
        readyBox.setDisable(true);
        readyInfo.setText("Waiting for other players to ready up...");
    }


    public void makeMove() {
        if (!(xField.getText().trim().isEmpty() && yField.getText().trim().isEmpty())){
            writeServer("Move " + xField.getText() + " " + yField.getText());
        } else {
            showError("Invalid move coordinates.");
        }
    }

    public void sendChat() {
        if (!chatField.getText().trim().isEmpty()){
            writeServer("Chat " + chatField.getText());
            messageArea.appendText("Me: " + chatField.getText() + "\r\n");
            chatField.setText("");
        }
    }


    @Override
	public void drawBoard() {

	}

	@Override
	public void showMessage(String message) {
        messageArea.setEditable(true);
        messageArea.appendText(message + "\r\n");
        messageArea.setEditable(false);
	}

	@Override
	public void showError(String error) {
        errorField.setText("ERROR: " + error);
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
    public void showPlayers(String players) {
        //todo
    }

    @Override
    public void showChallenge(String challenge) {
        //todo
    }

    @Override
    public void showLeaderboard(String leaderboard) {
        //todo
    }

    @Override
    public void setLogin(boolean success) {
        //todo
    }

    @Override
	public void update(Observable o, Object arg) {
	}

    @Override
    public void run() {
    }
}

