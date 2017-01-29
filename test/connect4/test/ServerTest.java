package connect4.test;

import connect4.game.GameView;
import connect4.network.client.Client;
import connect4.network.server.Lobby;
import connect4.network.server.Server;
import connect4.network.server.ServerStarter;
import connect4.ui.Tui;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;

import static org.junit.Assert.*;

public class ServerTest {

	Client client;

	//ServerStarter is modified to work with this test (It has been extended by Thread)
	//Otherwise the main thread will be stuck accepting connections from clients and
	//the program will not advance further.
	@Before
	public void setUp() throws Exception {
		String[] serverargs = {"2018"};
		ServerStarter starter = new ServerStarter("2018");
		starter.start();
		GameView tui = new Tui();
		client = new Client(tui);
		tui.setClient(client);

	}

	@Test
	public void connectionTest() {
		try {
			client.connectServer(2018, InetAddress.getLocalHost());
		} catch (IOException e) {
			System.out.println("Could not connect");
		}
		//Has a connection
		assertTrue(client.getServer() != null);
	}

	@Test
	public void commandTest() {
		connectionTest();
		try {
			client.writeServer("Join Nick chat leaderboard challenge security");
			client.writeServer("NotAValidCommand");
		} catch (IOException e) {
			System.out.println("Could not write to server");
		}
		//Sleep so the server has time to process it and not let the test shutdown.
		try {
			Thread.sleep(1000);
		} catch (InterruptedException e) {
			System.out.println("Main thread interrupted");
		}
		//Connect a second client to start a game.
		GameView tui2 = new Tui();
		Client client2 = new Client(tui2);
		tui2.setClient(client2);
		try {
			client2.connectServer(2018, InetAddress.getLocalHost());
		} catch (IOException e) {
			System.out.println("Could not connect");
		}
		//Both clients say they are ready.
		//In the console the board should now be visible (because a game has started)
		try {
			client2.writeServer("Join Julian chat leaderboard challenge security");
			client2.writeServer("Ready");
			client.writeServer("Ready");
		} catch (IOException e) {
			e.printStackTrace();
		}
		//Sleep to make time for the server to process it. And for the person running this test to see if everything is alright.
		try {
			Thread.sleep(1000);
		} catch (InterruptedException e) {
			System.out.println("Main thread interrupted");
		}
		//Make 1 client win the game. Console should read Nick or Julian has won.
		//Also 1 client tries to make a move again before it is his turn again (happens 4 or 5 times).
		//This should cause an error message.
		//This looks horrible because 2 clients and 1 server will use the same console.
		//But we can't test thing otherwise because you can't test what is printed.
		//It could be done by modifying the files to return something instead of void but this will take to much time
		//and it will likely break the implementation.
		try {
			for(int i = 0; i < 4; i++) {
				client.writeServer("Move " + i + " " + 0);
				Thread.sleep(1000);
				client.writeServer("Move " + i + " " + 0);
				Thread.sleep(1000);
				client2.writeServer("Move " + i + " " + 2);
				Thread.sleep(1000);
			}

		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		try {
			Thread.sleep(5000);
		} catch (InterruptedException e) {
			System.out.println("Main thread interrupted");
		}
		//To show the clients are back in the lobby we start a new game.
		try {
			client2.writeServer("Ready");
			client.writeServer("Ready");
		} catch (IOException e) {
			e.printStackTrace();
		}
		try {
			Thread.sleep(1000);
		} catch (InterruptedException e) {
			System.out.println("Main thread interrupted");
		}
		try {
			for(int i = 0; i < 4; i++) {
				client.writeServer("Move " + i + " " + 0);
				Thread.sleep(1000);
				client.writeServer("Move " + i + " " + 0);
				Thread.sleep(1000);
				client2.writeServer("Move " + i + " " + 2);
				Thread.sleep(1000);
			}

		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		try {
			Thread.sleep(5000);
		} catch (InterruptedException e) {
			System.out.println("Main thread interrupted");
		}
		//Back in the lobby the client wants to know the leaderboard
		//A client asks the leaderboard
		//It should print out a top 10 of usernames and scores
		try {
			client.writeServer("Leaderboard");
			Thread.sleep(5000);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		//The client wants to login/register
		//It should print Login Success or Login Denied if the account already exist
		//Client2 also tries to login into the same account with another password
		try {
			client.writeServer("Security Nick Thisismypassword");
			Thread.sleep(1000);
			client2.writeServer("Security Nick Nottherightpassword");
			Thread.sleep(5000);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		//Client wants to challenge client2
		//First he asks who he can challenge by the command GetPlayers
		try {
			client.writeServer("GetPlayers");
			Thread.sleep(1000);
			client.writeServer("Challenge 4 2 Julian");
			Thread.sleep(2000);
			client2.writeServer("ChallengeAccept y");
			Thread.sleep(2000);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		//And now a normal game between them is started
		//But client2 wants to leave
		//They both go to the lobby again
		try {
			client2.writeServer("Leave");
			Thread.sleep(1000);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		//And now they want to chat a bit
		try {
			client2.writeServer("Chat Hey how are you doing?");
			Thread.sleep(1000);
			client.writeServer("Chat Hey, I am doing fine, and you?");
			Thread.sleep(1000);
			client2.writeServer("Chat Same, playing some board game called Connect4-3D or Score Four");
			Thread.sleep(1000);
			client.writeServer("Chat What a coincidence, me too");
			Thread.sleep(1000);

		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		//Another challenge but this time it is denied
		try {
			client.writeServer("GetPlayers");
			Thread.sleep(1000);
			client.writeServer("Challenge 4 2 Julian");
			Thread.sleep(2000);
			client2.writeServer("ChallengeAccept n");
			Thread.sleep(2000);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}



	}

}