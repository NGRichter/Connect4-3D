package connect4.network;


import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;


public class Peer implements Runnable {

    public static final String EXIT = "exit";

    protected String name;
    protected Socket sock;
    protected BufferedReader in;
    protected BufferedWriter out;

    public Peer(String nameArg, Socket sockArg){
        this.name = nameArg;
        this.sock = sockArg;
        try {
            this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
            this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    @Override
    public void run() {
        while(true){
            String msgIn = "";
            try {
                msgIn = in.readLine();
            } catch (IOException e){
                break;
            }
            if(msgIn == null){
                break;
            }
            System.out.println(msgIn);
        }
    }


    // Returns name of peer object
    public String getName() {
        return name;
    }

    public void shutDown(){
        try {
            in.close();
            out.close();
            sock.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    // Read string entered by user
    public String readString(String text){
        String line = null;
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
            line = in.readLine();
        } catch (IOException e) {
            e.printStackTrace();
        }

        return (line == null) ? "" : line;
    }


    // Send input string
    public void handleTerminalInput() {
        String msgOut = "";
        while(true){
            msgOut = readString("");
            if (msgOut.equals(Peer.EXIT)){
                shutDown();
            }
            try {
                out.write(msgOut + "\n");
                out.flush();
            } catch (IOException e){
                e.printStackTrace();
            }
        }
    }
}
