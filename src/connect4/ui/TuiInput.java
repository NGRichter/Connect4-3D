package connect4.ui;

import java.util.Scanner;

import connect4.network.Buffer;

public class TuiInput extends Thread {
	
	private Buffer buffer;
	
	public TuiInput(Buffer buffer) {
		this.buffer = buffer;
	}
	
	public void run() {
        Scanner scan = new Scanner(System.in);
        while(true) {
                String input = scan.nextLine();
                buffer.writeBuffer(input);
        }
	}

}
