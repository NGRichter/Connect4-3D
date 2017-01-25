package connect4.bonus;

import java.io.*;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.List;

public class Leaderboard {

	public List<Score> scores = new ArrayList<Score>();
	private BufferedReader reader;
	private FileWriter writer;

	public Leaderboard(String path) {
		try {
			File file = new File(path);
			writer = new FileWriter(file, true);
			reader = new BufferedReader(new FileReader(file));
			String temp;
			while ((temp = reader.readLine()) != null) {
				String[] temp2 = temp.split(" ");
				String[] temp3 = temp2[2].split("/");
				String[] temp4 = temp2[3].split(":");
				Score score = new Score(Integer.parseInt(temp3[2]), Integer.parseInt(temp3[1]), Integer.parseInt(temp3[0]), Integer.parseInt(temp4[0]), Integer.parseInt(temp4[1]), Integer.parseInt(temp2[1]), temp2[0]);
				scores.add(score);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void addScore(Score score) {
		scores.add(score);
		try {
			writer.write("\n" + score.toString());
			writer.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public String topN(int n) {
		String leaderboard = "";
		sortScore();
		for (int i = 0; i < n; i++) {
			leaderboard += scores.get(i) + "\n";
		}
		return leaderboard;
	}

	public String aboveN(int n) {
		String leaderboard = "";
		sortScore();
		for (Score score : scores) {
			if (score.score > n) {
				leaderboard += score.toString() + "\n";
			}
		}
		return leaderboard;
	}

	public String belowN(int n) {
		String leaderboard = "";
		sortScore();
		for (Score score : scores) {
			if (score.score < n) {
				leaderboard += score.toString() + "\n";
			}
		}
		return leaderboard;
	}

	public int averageScore() {
		int leaderboard = 0;
		int i = 0;
		for (Score score : scores) {
			leaderboard += score.score;
			i++;
		}
		return leaderboard / i;
	}

	public int averageScoreToday() {
		int leaderboard = 0;
		int i = 0;
		for (Score score : scores) {
			if (isToday(score.date)) {
				leaderboard += score.score;
				i++;
			}
		}
		return leaderboard / i;
	}

	public String scoresToday() {
		String leaderboard = "";
		sortScore();
		for (Score score : scores) {
			if (isToday(score.date)) {
				leaderboard += score.toString() + "\n";
			}
		}
		return leaderboard;
	}

	public String bestToday() {
		sortScore();
		for (Score score : scores) {
			if (isToday(score.date)) {
				return score.toString() + "\n";
			}
		}
		return "No score today";
	}

	public String bestOfPerson(String name) {
		sortScore();
		for (Score score : scores) {
			if (score.name.equals(name)) {
				return score.toString();
			}
		}
		return "Person has no score";
	}

	public void sortScore() {
		Score temp;
		for (int i = 0; i < scores.size(); i++) {
			for (int o = 1; o < scores.size() - i; o++) {
				if (scores.get(o - 1).score < scores.get(o).score) {
					temp = scores.get(o);
					scores.set(o, scores.get(o - 1));
					scores.set(o - 1, temp);
				}
			}
		}
	}

	public void sortTime() {
		Score temp;
		for (int i = 0; i < scores.size() - 1; i++) {
			for (int o = 1; o < scores.size() - i; o++) {
				if (scores.get(o - 1).date.compareTo(scores.get(o).date) < 0) {
					temp = scores.get(o);
					scores.set(o, scores.get(o - 1));
					scores.set(o - 1, temp);
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

	public boolean isToday(Date date) {
		Calendar cal1 = Calendar.getInstance();
		Calendar cal2 = Calendar.getInstance();
		cal1.setTime(date);
		cal2.setTime(Calendar.getInstance().getTime());
		return (cal1.get(Calendar.ERA) == cal2.get(Calendar.ERA) &&
				cal1.get(Calendar.YEAR) == cal2.get(Calendar.YEAR) &&
				cal1.get(Calendar.DAY_OF_YEAR) == cal2.get(Calendar.DAY_OF_YEAR));
	}

}
