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
			client.writeServer("Join Nick");
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
			client2.writeServer("Join Julian");
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

	}

}