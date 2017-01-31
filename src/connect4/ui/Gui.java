package connect4.ui;

import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.Board;
import connect4.game.Game;
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

import static javafx.scene.transform.Rotate.Z_AXIS;

public class Gui extends Application implements GameView, Initializable {

	//Application settings
	private final int HEIGHT = 1280;
	private final int WIDTH = 720;
	private boolean RESIZABLE;
	//3D Scene settings
	private final int SCENE3DHEIGHT = 675;
	private final int SCENE3DWIDTH = 970;
	private Stage window;
	private Client client;
	private Scene scene;
	@FXML
	private Button connectButton, joinButton, moveButton, readyButto, challengeButton;
	@FXML
	private TextField ipField, portField, usernameField, chatField, xField,
			yField, boardDimField, playerAmountField, challengeNameField;
	@FXML
	private TextArea messageArea, chatArea;
	@FXML
	private Label errorField, readyInfo;
	@FXML
	private RadioButton noRoofButton;
	@FXML
	private PasswordField passwordField;
	@FXML
	private HBox connectBox, joinBox, lobbyTools, gameTools, challengeControls;
	@FXML
	private VBox readyBox, challengeBox;
	@FXML
	private Parent root, game;
	@FXML
	private BorderPane gamePane;
	@FXML
	private StackPane centerPane;
	@FXML
	private Pane connectPane, lobbyPane, boardPane;
	@FXML
	private PerspectiveCamera camera;
	@FXML
	private Group boardGroup;
	private SubScene scene3d;
	private PhongMaterial gridMaterial;


	@Override
	public void init() {
		client = new Client(this);
	}

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		client = new Client(this);
		//Initialize the stackpane setup.
		//Within the gamepane
		boardPane.toBack();
		boardPane.setVisible(false);
		lobbyPane.toFront();
		lobbyPane.setVisible(true);
		gameTools.setVisible(false);

		//Between gamepane and connectpane
		gamePane.setVisible(false);
		gamePane.toBack();
		connectPane.setVisible(true);
		connectPane.toFront();


		boardGroup = new Group();
		boardGroup.setTranslateX(SCENE3DWIDTH / 2);
		boardGroup.setTranslateY(SCENE3DHEIGHT / 2);

		gridMaterial = new PhongMaterial();
		gridMaterial.setSpecularColor(Color.WHITE);
		gridMaterial.setDiffuseColor(Color.WHITE);

		scene3d = createScene3D(boardGroup);
		boardPane.getChildren().add(scene3d);
	}

	public SubScene createScene3D(Group group) {
		SubScene scene3d = new SubScene(group, SCENE3DWIDTH, SCENE3DHEIGHT, true, SceneAntialiasing.BALANCED);
		scene3d.setFill(Color.rgb(10, 10, 40));
		camera = new PerspectiveCamera();
		camera.setRotationAxis(Rotate.X_AXIS);
		camera.setRotate(27.5);
		scene3d.setCamera(camera);
		return scene3d;
	}


	@Override
	public void start(Stage primaryStage) throws Exception {
		window = primaryStage;
		window.setTitle("Connect4-3D GUI client");
		window.setResizable(RESIZABLE);

		root = FXMLLoader.load(getClass().getResource("fxml/stackedUI.fxml"));
		Platform.setImplicitExit(false);
		scene = new Scene(root);

		primaryStage.setScene(scene);
		primaryStage.show();
	}

	public void connect() {
		if (usernameField.getText().trim().isEmpty()) {
			showError("Please specify a username.");
		} else try {
			InetAddress address = InetAddress.getByName(ipField.getText());
			int port = Integer.parseInt(portField.getText());
			client.connectServer(port, address);
			writeServer("Join " + usernameField.getText() + " chat security challenge leaderboard");
			if (!(passwordField.getText().trim().isEmpty())) {
				writeServer("Security " + usernameField.getText() + " " + passwordField.getText());
			}
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

	public void disconnect() {
		writeServer("Disconnect");
		client.stopClientGame();
		client.serverDisconnected();
		gameOver();
		connectPane.toFront();
		connectPane.setVisible(true);
		gamePane.toBack();
		gamePane.setVisible(false);
	}

	public void leave() {
		writeServer("Leave");
		client.stopClientGame();
		gameOver();
	}

	public void leaderboard() {
		writeServer("Leaderboard");
	}

	public void setReady() {
		int playerAmount = 2;
		int boardDim = 4;
		String noRoof = "";
		if (!(playerAmountField.getText().trim().isEmpty())) {
			playerAmount = Integer.parseInt(playerAmountField.getText());
		}
		if (!(boardDimField.getText().trim().isEmpty())) {
			boardDim = Integer.parseInt(boardDimField.getText());
		}
		writeServer("Ready " + playerAmount + " " + boardDim + " " + noRoof);
		readyBox.setDisable(true);
		challengeBox.setDisable(true);
		readyInfo.setVisible(true);
		readyInfo.setText("Waiting for other players to ready up...");
	}


	public void makeMove() {
		if (!(xField.getText().trim().isEmpty() && yField.getText().trim().isEmpty())) {
			writeServer("Move " + xField.getText() + " " + yField.getText());
		} else {
			showError("Invalid move coordinates.");
		}
	}

	public void sendChat() {
		if (!chatField.getText().trim().isEmpty()) {
			Platform.runLater(new Runnable() {
				@Override
				public void run() {
					writeServer("Chat " + chatField.getText());
					chatArea.appendText("Me: " + chatField.getText() + "\r\n");
					chatField.setText("");
				}
			});
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

				Group boardGroup = new Group();
				boardGroup.setTranslateX(SCENE3DWIDTH / 2 - ((board.getDimX()) * 25));
				boardGroup.setTranslateY(SCENE3DHEIGHT / 2);

				drawGrid(board, boardGroup);

				for (int z = 0; z < board.getDimZ() && z >= 0; z++) {
					for (int x = 0; x < board.getDimX(); x++) {
						for (int y = 0; y < board.getDimY(); y++) {
							Player player = null;
							try {
								player = board.getField(x, y, z);
							} catch (OutsidePlayingBoardException e) {
								e.printStackTrace();
							}
							if (player != null) {
								Color color = player.getColour();
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
					POSZ = POSZ - OFFSETZ;
				}

				boardGroup.setRotationAxis(Z_AXIS);
				boardGroup.setRotate(45);

				RotateTransition rt = new RotateTransition(Duration.seconds(45), boardGroup);
				rt.setCycleCount(Animation.INDEFINITE);
				rt.setFromAngle(0);
				rt.setToAngle(360);
				rt.setAutoReverse(false);
				rt.setAxis(Z_AXIS);
				rt.play();

				scene3d.setRoot(boardGroup);
			}
		});
	}

	public void drawGrid(Board board, Group boardGroup) {
		int POSX = 0;
		int POSY = 0;
		int POSZ = 0;
		int OFFSETX = 50;
		int OFFSETY = 50;

		for (int x = 0; x < board.getDimX(); x++) {
			for (int y = 0; y < board.getDimY(); y++) {

				Color color = Color.WHITE;

				Box grid = new Box();
				grid.setHeight(15.0);
				grid.setWidth(15.0);
				grid.setDepth(2.0);
				PhongMaterial boxMaterial = new PhongMaterial();
				boxMaterial.setDiffuseColor(color);
				boxMaterial.setSpecularColor(color);
				grid.setMaterial(boxMaterial);
				grid.setTranslateX(POSX);
				grid.setTranslateY(POSY);
				grid.setTranslateZ(POSZ);
				grid.setDrawMode(DrawMode.FILL);
				boardGroup.getChildren().add(grid);

				POSY = POSY + OFFSETY;
			}
			POSY = 5;
			POSX = POSX + OFFSETX;
		}
	}

	@Override
	public void showMessage(String message) {
		Platform.runLater(new Runnable() {
			@Override
			public void run() {
				messageArea.setEditable(true);
				messageArea.appendText(message + "\r\n");
				messageArea.setEditable(false);
			}
		});
	}

	@Override
	public void showChat(String chatmessage) {
		Platform.runLater(new Runnable() {
			@Override
			public void run() {
				chatArea.setEditable(true);
				chatArea.appendText(chatmessage + "\r\n");
				chatArea.setEditable(false);
			}
		});
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

	public Client getClient() {
		return client;
	}

	@Override
	public void setClient(Client client) {
		this.client = client;
	}

	@Override
	public void gameStarted() {
		Platform.runLater(new Runnable() {
			@Override
			public void run() {
				lobbyPane.setVisible(false);
				lobbyPane.toBack();
				boardPane.toFront();
				boardPane.setVisible(true);
				gameTools.setVisible(true);
				drawBoard();
				showMessage("It is the turn of " + client.getGame().getCurrentPlayer().getName());
			}
		});
	}

    @Override
    public void gameOver() {
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
                lobbyPane.setVisible(true);
                lobbyPane.toFront();
                boardPane.toBack();
                boardPane.setVisible(false);
                gameTools.setVisible(false);
                readyBox.setDisable(false);
                readyInfo.setVisible(false);
                challengeBox.setDisable(false);
                challengeControls.setDisable(true);
            }
        });
    }

	@Override
	public void showPlayers(String players) {
		String[] player = players.split(" ");
		if (player[0].equals("AllPlayers")) {
			String toScreen = "All players in the lobby:";
			for (int i = 1; i < player.length; i++) {
				if (player[i].equals("Game")) {
					toScreen += "\r\nAll players in a game:";
				} else {
					toScreen += "\r\n" + player[i];
				}
			}
			showMessage(toScreen);
		} else if (player[0].equals("Players")) {
			String toScreen = "All players you can challenge:";
			for (int i = 1; i < player.length; i++) {
				toScreen += "\r\n" + player[i];
			}
			showMessage(toScreen);
		}
	}

	@Override
	public void showChallenge(String challenge) {
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
                showMessage("CHALLENGE RECEIVED");
                if (!challenge.equals("ChallengeDenied")) {
                    challengeControls.setDisable(false);
                    String[] challenges = challenge.split(" ");
                    if (challenges.length >= 3){
                        String challengeMsg = String.format("You've been challenged: %s%nDimension:" +
                                " %s%nPlayers: %s%nWith roof%n.-------", challenges[3], challenges[1], challenges[2]);
                        showMessage(challengeMsg);
                    } else if (challenges.length >= 4 && challenges[3].equals("NoRoof")){
                        String challengeMsg = String.format("You've been challenged: %s%nDimension:" +
                                " %s%nPlayers: %s%nWith no roof%n-------", challenges[4], challenges[1], challenges[2]);
                        showMessage(challengeMsg);
                    }
                } else {
                    showMessage("Challange has been denied.");
                    gameOver();
                }
            }
        });
	}

    public void challengePlayer(){
        Platform.runLater(new Runnable() {
            @Override
            public void run() {
                int playerAmount = 2;
                int boardDim = 4;
                String noRoof = "";
                if (!(playerAmountField.getText().trim().isEmpty())) {
                    playerAmount = Integer.parseInt(playerAmountField.getText());
                }
                if (!(boardDimField.getText().trim().isEmpty())) {
                    boardDim = Integer.parseInt(boardDimField.getText());
                }
                if (!challengeNameField.getText().trim().isEmpty()) {
                    writeServer("Challenge " + boardDim + " " + playerAmount + " " + noRoof + challengeNameField.getText());
                    readyBox.setDisable(true);
                    challengeBox.setDisable(true);
                    readyInfo.setVisible(true);
                    readyInfo.setText("Waiting for challenge response...");
                }
            }
        });
    }

    public void acceptChallenge(){
        writeServer("ChallengeAccept y");
    }
    public void denyChallenge() {
        writeServer("ChallengeAccept n");
    }

	@Override
	public void showLeaderboard(String leaderboard) {
		String[] leaderboards = leaderboard.split(" ");
		String score = "---Leaderboard---";
		for (int i = 1; i < leaderboards.length; i += 2) {
			score += "\r\n" + leaderboards[i] + " - " + leaderboards[i + 1];
		}
		showMessage(score);
	}

	@Override
	public void setLogin(boolean success) {
		if (success) {
			showMessage("Login successful.");
		} else {
			showMessage("Login failed.");
		}
	}

	@Override
	public void update(Observable o, Object arg) {
		if (o instanceof Game) {
			drawBoard();
			showMessage(arg + " has made a move.");
			showMessage("It is the turn of " + client.getGame().getCurrentPlayer().getName());
			if (client.getGame().getCurrentPlayer() == client.getAI()) {
				int[] xy = client.getAI().determineMove(client.getGame(), client.getThinkingtime());
				writeServer("Move " + xy[0] + " " + xy[1]);
			}
		}
	}

	@Override
	public void run() {
	}
}

