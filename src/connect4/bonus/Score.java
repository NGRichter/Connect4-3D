package connect4.bonus;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;

public class Score {

	public Date date;
	public int score;
	public String name;

	/**
	 * Makes a new score used by leaderboard.
	 * @param year - the year in which the score was made
	 * @param month - the month in which the score was made
	 * @param day - the day_of_month in which the score was made
	 * @param hour - the hour_of_day in which the score was made
	 * @param minute - the minute_of_hour in which the score was made
	 * @param score - the score
	 * @param name - the name of the person who made the score
	 */
	public Score(int year, int month, int day, int hour, int minute, int score, String name) {
		try {
			this.date = new SimpleDateFormat("dd/MM/yyyy HH:mm").parse(day + "/" + month + "/" + year + " " + hour + ":" + minute);
		} catch (ParseException e) {
			System.out.println("Can't create date");
		}
		this.score = score;
		this.name = name;
	}

	/**
	 * Makes a string representing the score
	 * @return string with formatting: "name score dd/MM/yyyy HH:mm"
	 */
	public String toString() {
		SimpleDateFormat format = new SimpleDateFormat("dd/MM/yyyy HH:mm");
		return name + " " + score + " " + format.format(date);
	}
}
