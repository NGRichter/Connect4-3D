package connect4.network.server;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class Buffer {

	private final Lock lock;
	private /*@ spec_public @*/ boolean isEmpty;
	private /*@ spec_public @*/ List<String> buffer;

	/**
	 * Makes a new Buffer which is empty.
	 */
	public Buffer() {
		buffer = new ArrayList<String>();
		isEmpty = true;
		lock = new ReentrantLock();
	}

	/**
	 * Reads one string from the buffer and sets isEmpty to true if it was the only string.
	 * Will read at first index and remove the first index. 
	 * All elements will be shifted to the left.
	 * @return String that was stored
	 */
	//@ requires !isEmpty; 
	public String readBuffer() {
		synchronized (lock) {
			if (buffer.size() >= 1) {
				String temp = buffer.get(0);
				buffer.remove(0);
				if (buffer.isEmpty()) {
					isEmpty = true;
				}
				return temp;
			} else {
				return null;
			}
		}

	}

	/**
	 * Writes a String to the buffer, if it was empty before set isEmpty to false.
	 * @param string - The string you want to store in the buffer
	 */
	//@ ensures buffer.contains(string);
	public void writeBuffer(String string) {
		synchronized (lock) {
			if (buffer.isEmpty()) {
				isEmpty = false;
			}
			buffer.add(string);
		}
	}

	/**
	 * Returns true if the buffer is empty, false if it is not.
	 * @return true if empty, false if not empty
	 */
	//@ ensures \result == buffer.isEmpty();
	//@ pure
	public boolean isEmpty() {
		synchronized (lock) {
			return isEmpty;
		}
	}
}
