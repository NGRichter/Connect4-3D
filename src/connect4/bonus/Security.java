package connect4.bonus;

import org.apache.commons.codec.binary.Hex;

import java.io.*;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.Map;

public class Security {

	private Map<String, String> accounts = new HashMap<String, String>();
	private BufferedReader reader;
	private FileWriter writer;

	/**
	 * Makes a new security object which reads all data from a storage file and puts it in a map.
	 * @param path - path to the storage file
	 */
	public Security(String path) {
		try {
			File file = new File(path);
			writer = new FileWriter(file, true);
			reader = new BufferedReader(new FileReader(file));
			String temp;
			while ((temp = reader.readLine()) != null) {
				String[] temp2 = temp.split(" ");
				accounts.put(temp2[0], temp2[1]);
			}
		} catch (IOException e) {

		}

	}

	/**
	 * Registers a username and password, writes it to the storage file.
	 * @param username - username that you want registered
	 * @param password - password you want registered
	 */
	//@ requires username != null && password != null;
	public void register(String username, String password) {
		String saltedPassword = password + username + username.substring(0, 1);
		try {
			MessageDigest md = MessageDigest.getInstance("SHA-256");
			byte[] bytearray = md.digest(saltedPassword.getBytes());
			accounts.put(username, Hex.encodeHexString(bytearray));
			if (accounts.size() == 1) {
				writer.write(username + " " + Hex.encodeHexString(bytearray));
				writer.flush();
			} else {
				writer.write("\r\n" + username + " " + Hex.encodeHexString(bytearray));
				writer.flush();
			}

		} catch (NoSuchAlgorithmException e) {

		} catch (IOException e) {
		}

	}

	/**
	 * Verifies if the username and password specified is the same as stored.
	 * If username is not stored yet register the user.
	 * @param username
	 * @param password
	 * @return true if successfully logged in or registered, false if password is not the same as stored
	 */
	//@ requires username != null && password != null;
	public boolean login(String username, String password) {
		if (accounts.containsKey(username)) {
			String saltedPassword = password + username + username.substring(0, 1);
			try {
				MessageDigest md = MessageDigest.getInstance("SHA-256");
				byte[] bytearray = md.digest(saltedPassword.getBytes());
				if (accounts.get(username).equals(Hex.encodeHexString(bytearray))) {
					return true;
				} else {
					return false;
				}
			} catch (NoSuchAlgorithmException e) {
				return false;
			}
		} else {
			register(username, password);
			return true;
		}
	}

}
