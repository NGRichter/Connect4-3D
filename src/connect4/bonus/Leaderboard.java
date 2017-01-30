package connect4.bonus;

import java.io.*;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.List;

public class Leaderboard {

	private /*@ spec_public @*/ List<Score> scores;
	private FileWriter writer;

	/**
	 * Makes a leaderboard that reads initial values from a storage file.
	 * @param path - path to the storage file
	 */
	public Leaderboard(String path) {
		scores = new ArrayList<>();
		try {
			File file = new File(path);
			file.mkdir();
			writer = new FileWriter(file, true);
			BufferedReader reader = new BufferedReader(new FileReader(file));
			String temp;
			while ((temp = reader.readLine()) != null) {
				String[] temp2 = temp.split(" ");
				String[] temp3 = temp2[2].split("/");
				String[] temp4 = temp2[3].split(":");
				Score score = new Score(Integer.parseInt(temp3[2]), Integer.parseInt(temp3[1]), Integer.parseInt(temp3[0]), Integer.parseInt(temp4[0]), Integer.parseInt(temp4[1]), Integer.parseInt(temp2[1]), temp2[0]);
				scores.add(score);
			}
			reader.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Adds a score to the list.
	 * Writes it to the file.
	 * @param score - score to be added
	 */
	//@ requires score != null;
	//@ ensures scores.contains(score);
	public void addScore(Score score) {
		scores.add(score);
		try {
			if (scores.size() == 1) {
				writer.write(score.toString());
				writer.flush();
			} else {
				writer.write("\r\n" + score.toString());
				writer.flush();
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Makes a string consisting of the top N places.
	 * @param n - how many places you want
	 * @return string with \r\n after every place
	 */
	//@ requires n >= 0;
	public String topN(int n) {
		String leaderboard = "";
		sortScore();
		if (n <= scores.size()) {
			for (int i = 0; i < n; i++) {
				leaderboard += scores.get(i) + " ";
			}
		} else {
			for (int i = 0; i < scores.size(); i++) {
				leaderboard += scores.get(i) + " ";
			}
		}

		return leaderboard;
	}

	/**
	 * Makes a string consisting of the scores above a certain value N.
	 * @param n - the value which the scores should be above
	 * @return string with \r\n after every place
	 */
	//@ requires n >= 0;
	public String aboveN(int n) {
		String leaderboard = "";
		sortScore();
		for (Score score : scores) {
			if (score.score > n) {
				leaderboard += score.toString() + "\r\n";
			}
		}
		return leaderboard;
	}

	/**
	 * Makes a string consisting of the scores below a certain value N.
	 * @param n - the value which the scores should be below
	 * @return string with \r\n after every place
	 */
	//@ requires n >= 0;
	public String belowN(int n) {
		String leaderboard = "";
		sortScore();
		for (Score score : scores) {
			if (score.score < n) {
				leaderboard += score.toString() + "\r\n";
			}
		}
		return leaderboard;
	}

	/**
	 * Returns an integer with the average score of all the scores.
	 * @return int of average score of all-time
	 */
	public int averageScore() {
		int leaderboard = 0;
		int i = 0;
		for (Score score : scores) {
			leaderboard += score.score;
			i++;
		}
		return leaderboard / i;
	}

	/**
	 * Returns an integer with the average score of all the scores of today.
	 * @return int of average score of today
	 */
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

	/**
	 * Makes a string consisting of all the scores of today
	 * @return string with \r\n after every place
	 */
	public String scoresToday() {
		String leaderboard = "";
		sortScore();
		for (Score score : scores) {
			if (isToday(score.date)) {
				leaderboard += score.toString() + "\r\n";
			}
		}
		return leaderboard;
	}

	/**
	 * Makes a string with the best score of today.
	 * @return string of best score
	 */
	public String bestToday() {
		sortScore();
		for (Score score : scores) {
			if (isToday(score.date)) {
				return score.toString() + "\r\n";
			}
		}
		return "No score today";
	}

	/**
	 * Makes a string with the best score of a person.
	 * @param name - name of person
	 * @return string of best score of that person
	 */
	public String bestOfPerson(String name) {
		sortScore();
		for (Score score : scores) {
			if (score.name.equals(name)) {
				return score.toString();
			}
		}
		return "Person has no score";
	}

	/**
	 * Sorts the score list from best to worst.
	 */
	private void sortScore() {
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

	/**
	 * Sorts the score list from newest to oldest.
	 */
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

	/**
	 * Makes a string of all the scores ever made.
	 * @return string with \r\n after every place
	 */
	public String toString() {
		String leaderboard = "";
		for (Score score : scores) {
			leaderboard += score + "\r\n";
		}
		return leaderboard;
	}

	/**
	 * Calculates if the date is today.
	 * @param date - the date you want to know if it is today
	 * @return true if it is today, false if it is not today
	 */
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
