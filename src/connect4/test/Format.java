package connect4.test;

public class Format {

	public static void main(String[] args) {

		String arr[][] = {
				{"Henk", "Harry", "Klaas"}, {"Frans", "Jacobienusje", "Matthijs"}
		};

		for (int row = 0; row < arr.length; row++) {
			for (int col = 0; col < arr[0].length; col++) {
				System.out.printf("| %-8s |", arr[row][col]);
			}
			System.out.printf("\r\n");
		}


	}
}
