package connect4.ui;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.GameView;
import connect4.game.Player;
import connect4.network.client.Client;
import javafx.animation.Animation;
import javafx.animation.RotateTransition;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.*;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.scene.paint.PhongMaterial;
import javafx.scene.shape.Box;
import javafx.scene.shape.DrawMode;
import javafx.scene.transform.Rotate;
import javafx.stage.Stage;
import javafx.util.Duration;

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

    //3D Scene settings
    private int SCENE3DHEIGHT = 675;
    private int SCENE3DWIDTH = 970;

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
    @FXML private StackPane centerPane;
    @FXML private Pane connectPane, lobbyPane, boardPane;
    @FXML private PerspectiveCamera camera;
    @FXML private Group boardGroup;
    private SubScene scene3d;

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

        boardGroup = new Group();
        boardGroup.setTranslateX(SCENE3DWIDTH/2);
        boardGroup.setTranslateY(SCENE3DHEIGHT/2);
        scene3d = createScene3D(boardGroup);
        boardPane.getChildren().add(scene3d);
    }

    public SubScene createScene3D(Group group){
        SubScene scene3d = new SubScene(group, SCENE3DWIDTH , SCENE3DHEIGHT, true, SceneAntialiasing.BALANCED);
        scene3d.setFill(Color.rgb(10, 10, 40));
        camera = new PerspectiveCamera();
        camera.setRotationAxis(Rotate.X_AXIS);
        camera.setRotate(35.0);
        scene3d.setCamera(camera);
        return scene3d;
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

        lobbyPane.setVisible(false);
        lobbyPane.toBack();
        boardPane.toFront();
        boardPane.setVisible(true);
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
        Platform.runLater(new Runnable() {
            @Override
            public void run() {


        Board board = client.getGame().getBoard();
        int POSX = 0;
        int POSY = 0;
        int POSZ = 0;
        int OFFSETX = 50;
        int OFFSETY = 50;
        int OFFSETZ = 50;

        for (int z = (board.getDimZ()-1); z < board.getDimZ() && z >= 0; z--){
            for (int x = 0; x < board.getDimX(); x++) {
                for (int y = 0; y < board.getDimY(); y++){
                    Player player = null;
                    try {
                        player = board.getField(x, y ,z);
                    } catch (OutsidePlayingBoardException e) {
                        e.printStackTrace();
                    }
                    if (player != null) {
                        Color color = Color.RED;
                        if (player.getName().equals("Nick")){
                            color = Color.GREEN;
                        }
                        Box box = new Box();
                        box.setHeight(25.0);
                        box.setWidth(25.0);
                        box.setDepth(25.0);
                        PhongMaterial boxMaterial = new PhongMaterial();
                        boxMaterial.setDiffuseColor(color);
                        boxMaterial.setSpecularColor(color);
                        box.setMaterial(boxMaterial);
                        box.setTranslateX(POSX);
                        box.setTranslateY(POSY);
                        box.setTranslateZ(POSZ);
                        box.setDrawMode(DrawMode.FILL);
                        boardGroup.getChildren().add(box);
                    }
                    POSY = POSY + OFFSETY;
                }
                POSY = 0;
                POSX = POSX + OFFSETX;
            }
            POSX = 0;
            POSZ = POSZ + OFFSETZ;
        }
        POSZ = 0;

                scene3d.setRoot(boardGroup);
                System.out.println("BOARD DRAWN!");
                System.out.println(boardGroup.getChildren().size());
            }
        });
	}

	@Override
	public void showMessage(String message) {
        messageArea.setEditable(true);
        messageArea.appendText(message + "\r\n");
        messageArea.setEditable(false);
	}

	@Override
	public void showError(String error) {
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
        errorField.setText("ERROR: " + error);
            }
        });
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

