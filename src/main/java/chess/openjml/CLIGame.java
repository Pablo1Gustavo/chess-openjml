package chess.openjml;

import java.util.Scanner;

import chess.openjml.moves.AlgebraicNotationParser;
import chess.openjml.moves.MovePair;
import chess.openjml.pieces.enums.Color;

public class CLIGame
{
    protected final Board board;
    protected Color currentTurn = Color.WHITE;
    
    public CLIGame(Board board)
    {
        this.board = board;
    }

    public void changeTurn()
    {
        currentTurn = currentTurn.opposite();
    }

    public void start()
    {
        Scanner scanner = new Scanner(System.in);

        System.out.println(board.toString());
        System.out.print(currentTurn.toString() + " > ");

        while(true)
        {
            String line = scanner.nextLine().trim().toLowerCase();

            if ("quit".equals(line) || "exit".equals(line))
            {
                System.out.println("Exiting...");
                break;
            }

            boolean validNotation = AlgebraicNotationParser.isSimpleFromToNotation(line);

            if (!validNotation)
            {
                System.out.println("Invalid notation. Please use simple from-to notation (e.g., e2 e4).");
                continue;
            }

            MovePair move = MovePair.fromString(line);

            if (!board.isValidMove(move))
            {
                System.out.println("Invalid move. Please try again.");
                continue;
            }
            
            board.movePiece(move);

            if (board.isInCheck(currentTurn))
            {
                System.out.println("Check!");
            }

            if (board.isCheckMate(currentTurn.opposite()))
            {
                System.out.println("Checkmate! " + currentTurn + " wins!");
                break;
            }

            changeTurn();
            System.out.println();
            System.out.println(board.toString());
            System.out.print(currentTurn.toString() + " > ");
        }

        scanner.close();
    }
}
