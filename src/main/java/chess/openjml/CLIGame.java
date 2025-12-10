package chess.openjml;

import java.util.Scanner;

import chess.openjml.game.Game;
import chess.openjml.game.MoveResult;
import chess.openjml.moves.MovePair;

public class CLIGame
{
    protected final Game game;
    
    public CLIGame(Game game)
    {
        this.game = game;
    }

    public void start()
    {
        Scanner scanner = new Scanner(System.in);

        System.out.println(game.getBoard().toString());
        System.out.print(game.getCurrentTurn().toString() + " > ");

        while(true)
        {
            String line = scanner.nextLine().trim().toLowerCase();

            if ("quit".equals(line) || "exit".equals(line))
            {
                System.out.println("Exiting...");
                break;
            }
            if("reset".equals(line))
            {
                game.reset();
                System.out.println("===== Game reset =====");
                System.out.println(game.getBoard().toString());
                System.out.print(game.getCurrentTurn().toString() + " > ");
                continue;
            }

            boolean validNotation = MovePair.SIMPLE_FROM_TO_NOTATION.matcher(line).matches();

            if (!validNotation)
            {
                System.out.println("Invalid notation. Please use simple from-to notation (e.g., e2 e4).");
                System.out.print(game.getCurrentTurn().toString() + " > ");
                continue;
            }

            MovePair move = MovePair.fromString(line);

            MoveResult result = game.move(move);

            if (result == MoveResult.INVALID)
            {
                System.out.println("Invalid move. Please try again.");
                continue;
            }

            if (result == MoveResult.CHECKMATE)
            {
                System.out.println("Checkmate! " + game.getCurrentTurn() + " wins!");
                break;
            }
            if (result == MoveResult.DRAW)
            {
                System.out.println("The game is a draw!");
                break;
            }
            if (result == MoveResult.CHECK)
            {
                System.out.println("Check!");
            }

            System.out.println();
            System.out.println(game.getBoard().toString());
            System.out.print(game.getCurrentTurn().toString() + " > ");
        }

        scanner.close();
    }
}
