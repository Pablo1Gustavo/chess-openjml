package chess.openjml;

import java.util.Scanner;
import java.util.regex.Pattern;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.BaseMove;

/**
 * Terminal interface for chess game
 */
public class App
{
    private static final Pattern CASTLE = Pattern.compile("^O-O(-O)?[+#]?$");
    private static final Pattern PIECE_MOVE = Pattern.compile("^[KQRBN](?:[a-h1-8]|[a-h][1-8])?x?[a-h][1-8][+#]?$");
    private static final Pattern PAWN_ADVANCE = Pattern.compile("^[a-h][1-8](?:=[QRBN])?[+#]?$");
    private static final Pattern PAWN_CAPTURE = Pattern.compile("^[a-h]x[a-h][1-8](?:=[QRBN])?[+#]?$");
    
    //@ spec_public
    private static Game game;

    //@ requires args != null;
    public static void main(String[] args)
    {
        System.out.println("♟ Chess Terminal ♟");
        System.out.println("Enter moves in SAN (e.g. e4, Nf3, O-O). Type 'quit' to exit, 'board' to show board.\n");
        
        game = new Game();
        showBoard();
        
        Scanner scanner = new Scanner(System.in);
        try
        {
            while (true)
            {
                System.out.print(game.getCurrentPlayer() == Color.WHITE ? "White > " : "Black > ");
                if (!scanner.hasNextLine()) break;
                
                String line = scanner.nextLine().trim();
                if (line.isEmpty()) continue;
                
                if ("quit".equalsIgnoreCase(line) || "exit".equalsIgnoreCase(line))
                {
                    System.out.println("Goodbye.");
                    break;
                }
                
                if ("board".equalsIgnoreCase(line))
                {
                    showBoard();
                    continue;
                }
                
                if ("reset".equalsIgnoreCase(line))
                {
                    game.reset();
                    System.out.println("Game reset.");
                    showBoard();
                    continue;
                }
                
                if (isValidMove(line))
                {
                    processMove(line);
                }
                else
                {
                    System.out.println("Invalid notation. Try: e4, Nf3, O-O, exd5, etc.");
                }
            }
        }
        finally
        {
            scanner.close();
        }
    }

    private static boolean isValidMove(String input)
    {
        if (input == null) return false;
        String s = input.trim();
        if (s.isEmpty()) return false;

        s = s.replace('0', 'O');
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++)
        {
            char c = s.charAt(i);
            char prev = (i > 0) ? s.charAt(i - 1) : '\0';
            if ((c == 'k' || c == 'q' || c == 'r' || c == 'b' || c == 'n' || c == 'o' ||
                 c == 'K' || c == 'Q' || c == 'R' || c == 'B' || c == 'N' || c == 'O') &&
                (i == 0 || prev == '=' || prev == '-'))
            {
                sb.append(Character.toUpperCase(c));
            }
            else
            {
                sb.append(Character.toLowerCase(c));
            }
        }
        String norm = sb.toString();

        if (CASTLE.matcher(norm).matches()) return true;
        if (PIECE_MOVE.matcher(norm).matches()) return true;
        if (PAWN_CAPTURE.matcher(norm).matches()) return true;
        if (PAWN_ADVANCE.matcher(norm).matches()) return true;

        return false;
    }

    private static void processMove(String san)
    {
        if (SANParser.parseSANAndMove(game, san))
        {
            BaseMove lastMove = game.getBoard().getLastMove();
            System.out.println("✓ Move: " + lastMove.getAlgebraicNotation());
            
            Color currentPlayer = game.getCurrentPlayer();
            
            // Check for checkmate
            if (game.isCheckmate(currentPlayer))
            {
                System.out.println("♔ CHECKMATE! " + (currentPlayer == Color.WHITE ? "Black" : "White") + " wins!");
                endGame(game);
                return;
            }
            
            // Check for stalemate
            if (game.isStalemate(currentPlayer))
            {
                System.out.println("♔ STALEMATE! Game is a draw.");
                endGame(game);
                return;
            }
            
            // Check if current player is in check
            if (game.isInCheck(currentPlayer))
            {
                System.out.println("⚠ " + currentPlayer + " is in check!");
            }
            
            showBoard();
        }
        else
        {
            System.out.println("✗ Illegal move.");
        }
    }

    private static void endGame(Game game)
    {
        showBoard();
        System.out.println("Game over. Type 'reset' to play again or 'quit' to exit.");

        try {
            game.writePGNFile();
        }
        catch (Exception e) {
            System.err.println("Error writing PGN file: " + e.getMessage());
        }
        finally {
            System.exit(0);
        }
    }
    
    private static void showBoard()
    {
        System.out.println("\n" + game.getBoard().toString());
    }
}
