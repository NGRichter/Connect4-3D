package connect4.bonus;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

public class Leaderboard {
	
	public List<Score> scores = new ArrayList<Score>();
	private BufferedReader reader;
	private FileWriter writer;
	
	public static void main(String[] args) {
		Leaderboard leader = new Leaderboard("Serverdata\\Leaderboard.txt");
		Score score = new Score(2017,1,23,538,"Nick");
		Score score2 = new Score(2017,1,23,539,"Nick");
		Score score3 = new Score(2017,1,23,540,"Nick");
		leader.addScore(score);
		leader.addScore(score2);
		leader.addScore(score3);
		leader.sortScore();
		System.out.println(leader.toString());
	}
	
	public Leaderboard(String path) {
		try {
			File file = new File(path);
			writer = new FileWriter(file, true);
			System.out.println("Reader");
			reader = new BufferedReader(new FileReader(file));
			String temp;
			while ((temp = reader.readLine()) != null) {
				String[] temp2 = temp.split(" ");
				String[] temp3 = temp2[2].split("/");
				Score score = new Score(Integer.parseInt(temp3[2]), Integer.parseInt(temp3[1]), Integer.parseInt(temp3[0]), Integer.parseInt(temp2[1]), temp2[0]);
				scores.add(score);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public void addScore(Score score) {
		scores.add(score);
		try {
			writer.write(score.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public String topN(int n) {
		String leaderboard = "";
		for (int i = 0; i < n; i++) {
			leaderboard += scores.get(i) + "\n";
		}
		return leaderboard;
	}
	
	public void sortScore() {
		Score temp;
		for (int i = 0; i < scores.size() - 1; i++) {
			for (int o = 0; o < scores.size() - i; o++) {
				if (scores.get(i).score < scores.get(i + 1).score) {
					temp = scores.get(i);
					scores.set(i, scores.get(i + 1));
					scores.set(i + 1, temp);
				}
			}
		}
	}
	
	public void sortTime() {
		Score temp;
		for (int i = 0; i < scores.size() - 1; i++) {
			for (int o = 0; o < scores.size() - i; o++) {
				if (scores.get(i).date.compareTo(scores.get(i + 1).date) < 0) {
					temp = scores.get(i);
					scores.set(i, scores.get(i + 1));
					scores.set(i + 1, temp);
				}
			}
		}		
	}
	
	public String toString() {
		String leaderboard = "";
		for (Score score : scores) {
			leaderboard += score + "\n";
		}
		return leaderboard;
	}

}
