package chess.openjml;

import java.util.Scanner;
import java.util.regex.Pattern;

/**
 * Simple terminal front-end for the chess app.
 * Reads moves from stdin and dispatches to a move processor.
 */
public class App {

    // Castling: O-O or O-O-O 
    private static final Pattern CASTLE = Pattern.compile("^O-O(-O)?[+#]?$");

    // Piece move: N, B, R, Q, K
    private static final Pattern PIECE_MOVE = Pattern.compile("^[KQRBN](?:[a-h1-8]|[a-h][1-8])?x?[a-h][1-8][+#]?$");

    // Pawn advance: e4 or e8=Q 
    private static final Pattern PAWN_ADVANCE = Pattern.compile("^[a-h][1-8](?:=[QRBN])?[+#]?$");

    // Pawn capture: exd5 or exd8=Q
    private static final Pattern PAWN_CAPTURE = Pattern.compile("^[a-h]x[a-h][1-8](?:=[QRBN])?[+#]?$");

    public static void main(String[] args) {
        System.out.println("Chess terminal - enter moves in standard algebraic notation (e.g. e4, Nf3, O-O). Type 'quit' to exit.");

        Scanner scanner = new Scanner(System.in);
        try {
            while (true) {
                System.out.print("> ");
                if (!scanner.hasNextLine()) break;
                String line = scanner.nextLine().trim();
                if (line.isEmpty()) continue;
                if ("quit".equalsIgnoreCase(line) || "exit".equalsIgnoreCase(line)) {
                    System.out.println("Goodbye.");
                    break;
                }

                if (isValidMove(line)) {
                    processMove(line);
                } else {
                    System.out.println("Invalid move notation. Supported: SAN (e.g. e4, Nf3, O-O, exd5, e8=Q).");
                }
            }
        } finally {
            scanner.close();
        }
    }

    /**
     * Check whether the given input is a valid-looking SAN string.
     */
    private static boolean isValidMove(String input) {
        if (input == null) return false;
        String s = input.trim();
        if (s.isEmpty()) return false;

        s = s.replace('0', 'O');
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            char prev = (i > 0) ? s.charAt(i - 1) : '\0';
            if ((c == 'k' || c == 'q' || c == 'r' || c == 'b' || c == 'n' || c == 'o' ||
                 c == 'K' || c == 'Q' || c == 'R' || c == 'B' || c == 'N' || c == 'O') &&
                (i == 0 || prev == '=' || prev == '-')) {
                sb.append(Character.toUpperCase(c));
            } else {
                sb.append(Character.toLowerCase(c));
            }
        }
        String norm = sb.toString();

        // Castling (O-O or O-O-O)
        if (CASTLE.matcher(norm).matches()) return true;

        // Piece moves like Nf3, R1e2, Qxe5+, etc.
        if (PIECE_MOVE.matcher(norm).matches()) return true;

        // Pawn capture or advance
        if (PAWN_CAPTURE.matcher(norm).matches()) return true;
        if (PAWN_ADVANCE.matcher(norm).matches()) return true;

        return false;
    }

    private static void processMove(String move) {
        System.out.println("Valid SAN move: " + move);
        // Future: integrate with game/board to validate and apply the SAN move.
    }
}
