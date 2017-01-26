package connect4.test;

import connect4.bonus.Leaderboard;
import connect4.bonus.Score;
import connect4.exceptions.NoEmptySpotException;
import connect4.exceptions.OutsidePlayingBoardException;
import connect4.game.AI.MinimaxAlpha;
import connect4.game.AI.MinimaxAlphaV2;
import connect4.game.Board;
import connect4.game.Colour;
import connect4.game.Game;
import connect4.game.Player;

import java.util.ArrayList;
import java.util.Calendar;
import java.util.List;

/**
 * Created by NickR on 26-1-2017.
 */
public class TestingAI {

	public static void main(String[] args) {
		Leaderboard leaderboard = new Leaderboard("Serverdata\\Leaderboard.txt");
		Board board = new Board(4,4,4);
		Player minimaxV2 = new MinimaxAlphaV2("v2", Colour.random());
		Player minimaxV1 = new MinimaxAlpha("v1", Colour.random());
		Player[] players = {minimaxV2, minimaxV1};
		int minimaxv1 = 0;
		int minimaxv2 = 0;
		int turns = 0;
		List<Integer> miniv1 = new ArrayList<>();
		List<Integer> miniv2 = new ArrayList<>();
		int draw = 0;
		long begin;
		long end;
		for (int i = 0; i < 1; i++) {
			Game game = new Game(board, players, 4);
			int[] xy = {-1, -1};
			while (!game.gameOver()) {
				if (game.getCurrentPlayer() == minimaxV1) {
					begin = System.currentTimeMillis();
					xy = minimaxV1.determineMove(game);
					end = System.currentTimeMillis();
					miniv1.add((int) (end - begin));
					System.out.println("V1 took: " + (end - begin));
					turns++;
				} else if (game.getCurrentPlayer() == minimaxV2){
					begin = System.currentTimeMillis();
					xy = minimaxV2.determineMove(game);
					end = System.currentTimeMillis();
					miniv2.add((int) (end - begin));
					System.out.println("V2 took: " + (end - begin));
					turns++;
				}
				try {
					game.makeNextMove(xy[0], xy[1]);
				} catch (NoEmptySpotException e) {
					System.out.println("No empty spot");
				} catch (OutsidePlayingBoardException e) {
					System.out.println("Outide of board");
				}
			}
			if (game.isWinner(minimaxV1)) {
				minimaxv1++;
			} else if (game.isWinner(minimaxV2)) {
				minimaxv2++;
			} else {
				draw++;
			}
		}
		System.out.println("V1: " + minimaxv1 + "\nV2: " + minimaxv2 + "\nDraw: " + draw);
		int average = 0;
		int max = 0;
		for (Integer ints : miniv1) {
			average += ints;
			if (ints > max) {
				max = ints;
			}
		}
		average = average / miniv1.size();
		System.out.println("MinimaxV1 Max: " + max + "\nMinimaxV1 Average: " + average);
		average = 0;
		max = 0;
		for (Integer ints : miniv2) {
			average += ints;
			if (ints > max) {
				max = ints;
			}
		}
		average = average / miniv2.size();
		System.out.println("MinimaxV2 Max: " + max + "\nMinimaxV2 Average: " + average);
		int scorevalue = board.getDimX() * board.getDimX() * board.getDimX() * 4 - turns * board.getDimX();
		if (scorevalue < 0) {
			scorevalue = 0;
		}
		Score score = new Score(Calendar.getInstance().get(Calendar.YEAR),
				Calendar.getInstance().get(Calendar.MONTH),
				Calendar.getInstance().get(Calendar.DAY_OF_MONTH),
				Calendar.getInstance().get(Calendar.HOUR_OF_DAY),
				Calendar.getInstance().get(Calendar.MINUTE),
				scorevalue, "MinimaxV2");
		leaderboard.addScore(score);
		System.out.println(turns);


	}
}
