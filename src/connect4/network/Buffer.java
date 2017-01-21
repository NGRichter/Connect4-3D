package connect4.network;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class Buffer {
	
	private boolean isEmpty;
	private List<String> buffer;
	private final Lock lock;
	
	public Buffer() {
		buffer = new ArrayList<String>();
		isEmpty = true;
		lock = new ReentrantLock();
	}
	
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
	
	public void writeBuffer(String string) {
		synchronized (lock) {
			if (buffer.isEmpty()) {
				isEmpty = false;
			}
			buffer.add(string);
		}
	}
	
	public boolean isEmpty() {
		synchronized (lock) {
			return isEmpty;
		}
	}
}
