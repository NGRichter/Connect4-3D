package connect4.bonus;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.security.MessageDigest;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.codec.digest.DigestUtils;

public class Security {
	
	private Map<String, String> accounts = new HashMap<String, String>();
	private BufferedReader reader;
	private PrintWriter writer;
	
	public Security(String path) {
		try {
			File file = new File(path);
			reader = new BufferedReader(new FileReader(file));
			writer = new PrintWriter(new BufferedWriter(new FileWriter(file)));
			String temp;
			while ((temp = reader.readLine()) != null) {
				String[] temp2 = temp.split(" ");
				accounts.put(temp2[0], temp2[1]);
			}
		} catch (IOException e) {

		}

	}
	
	public void register(String username, String password) {
		String saltedPassword = password + username + username.substring(0, 1);
		MessageDigest md = DigestUtils.getSha256Digest();
		byte[] passwordHash = md.digest(saltedPassword.getBytes());
		accounts.put(username, new String(passwordHash));
		writer.println(username + " " + passwordHash);
	}
	
	public boolean login(String username, String password) {
		if (accounts.containsKey(username)) {
			String saltedPassword = password + username + username.substring(0, 1);
			MessageDigest md = DigestUtils.getSha256Digest();
			byte[] passwordHash = md.digest(saltedPassword.getBytes());
			if (accounts.get(username).equals(new String(passwordHash))) {
				return true;
			} else {
				return false;
			}
		} else {
			register(username, password);
			return true;
		}
	}

}
