package chess.openjml;

import java.util.ArrayList;
import java.util.List;

import chess.openjml.moves.Position;
import chess.openjml.pieces.*;
import chess.openjml.pieces.enums.Color;

public class App
{
    public static void main( String[] args )
    {
        List<Piece> pieces = new ArrayList<>(List.of(
            // White pieces (bottom, rows 0-1)
            new Rook(new Position(0, 0), Color.WHITE),
            new Knight(new Position(0, 1), Color.WHITE),
            new Bishop(new Position(0, 2), Color.WHITE),
            new Queen(new Position(0, 3), Color.WHITE),
            new King(new Position(0, 4), Color.WHITE),
            new Bishop(new Position(0, 5), Color.WHITE),
            new Knight(new Position(0, 6), Color.WHITE),
            new Rook(new Position(0, 7), Color.WHITE),
            // Black pieces (top, rows 7-6)
            new Rook(new Position(7, 0), Color.BLACK),
            new Knight(new Position(7, 1), Color.BLACK),
            new Bishop(new Position(7, 2), Color.BLACK),
            new Queen(new Position(7, 3), Color.BLACK),
            new King(new Position(7, 4), Color.BLACK),
            new Bishop(new Position(7, 5), Color.BLACK),
            new Knight(new Position(7, 6), Color.BLACK),
            new Rook(new Position(7, 7), Color.BLACK)
        ));

        for (int col = 0; col < 8; col++)
        {
            pieces.add(new Pawn(new Position(1, col), Color.WHITE));
            pieces.add(new Pawn(new Position(6, col), Color.BLACK));
        }

        Board board = new Board(pieces, 8, 8);

        String mode = args.length > 0 ? args[0].toLowerCase() : "gui";
        
        if ("cli".equals(mode))
        {
            CLIGame cliGame = new CLIGame(board);
            cliGame.start();
        }
        else
        {
            new GUIGame(board);
        }
    }
}
