package chess.openjml.game;

import chess.openjml.Board;
import chess.openjml.moves.MovePair;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;

//@ non_null_by_default
public class Game
{
    //@ spec_public
    protected final Board initialBoard;
    //@ spec_public
    protected Board board;
    //@ spec_public
    protected Color currentTurn = Color.WHITE;

    //@ requires board != null;
    //@ ensures this.board == board;
    public Game(Board board)
    {
        this.board = board;
        this.initialBoard = board.clone();
    }

    //@ ensures \result == board;
    //@ pure
    public Board getBoard()
    {
        return board;
    }

    //@ ensures \result == currentTurn;
    //@ pure
    public Color getCurrentTurn()
    {
        return currentTurn;
    }

    //@ ensures currentTurn == Color.WHITE ==> currentTurn == Color.BLACK;
    //@ ensures currentTurn == Color.BLACK ==> currentTurn == Color.WHITE;
    public void changeTurn()
    {
        currentTurn = currentTurn.opposite();
    }

    //@ requires move != null;
    //@ ensures \result == MoveResult.INVALID ==> !board.isValidMove(move);
    public MoveResult move(MovePair move)
    {
        if (!board.isValidMove(move))
        {
            return MoveResult.INVALID;
        }

        board.movePiece(move);
        changeTurn();

        if (board.isCheckMate(currentTurn))
        {
            return MoveResult.CHECKMATE;
        }
        else if (board.isInCheck(currentTurn))
        {
            return MoveResult.CHECK;
        }
        else if (board.isDraw())
        {
            return MoveResult.DRAW;
        }

        return MoveResult.COMMON;
    }

    //@ ensures currentTurn == Color.WHITE;
    public void reset()
    {
        this.board = initialBoard.clone();
        this.currentTurn = Color.WHITE;
    }
    
    //@ ensures \result >= 0;
    //@ pure
    public int getCapturedPointsFor(Color color)
    {
        var currentPieces = board.getAllPieces();
        var initialPieces = initialBoard.getAllPieces();

        int opponentInitialPoints = initialPieces.stream()
            .filter(p -> p.isEnemy(color))
            .mapToInt(Piece::getPoints)
            .sum();

        int opponentCurrentPoints = currentPieces.stream()
            .filter(p -> p.isEnemy(color))
            .mapToInt(Piece::getPoints)
            .sum();

        return opponentInitialPoints - opponentCurrentPoints;
    }
}
