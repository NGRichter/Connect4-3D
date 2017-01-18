package connect4.ui;

import javafx.application.Application;
import javafx.stage.Stage;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.layout.StackPane;


public class TestGUI extends Application implements EventHandler<ActionEvent> {;

    public static void main(String[] args) {
        launch(args);
    }

    Button button;

    @Override
    public void start(Stage primaryStage) {
        primaryStage.setTitle("Connect4-3D Superior client");

        button = new Button("Join");
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
            System.out.println("beep boop");
        }
    }
}
