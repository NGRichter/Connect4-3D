package connect4.bonus;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;

public class Score {
	
	public Date date;
	public int score;
	public String name;
	
	public Score(int year, int month, int day, int score, String name) {
		try {
			this.date = new SimpleDateFormat("dd/MM/yyyy").parse(day + "/" + month + "/" + year);
		} catch (ParseException e) {
			System.out.println("Can't create date");
		}
		this.score = score;
		this.name = name;
	}
	
	public String toString() {
		SimpleDateFormat format = new SimpleDateFormat("dd/MM/yyyy");
		return name + " " + score + " " + format.format(date);
	}
}