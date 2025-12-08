package chess.openjml.moves;

import chess.openjml.pieces.enums.Color;

/**
 * Represents a castling move (kingside or queenside).
 */
//@ non_null_by_default
public class CastlingMove extends BaseMove
{
    //@ spec_public
    private final boolean kingSide;
    //@ spec_public
    private final boolean queenSide;
    
    //@ public invariant kingSide || queenSide;
    //@ public invariant !(kingSide && queenSide);
    
    //@ requires from != null;
    //@ requires to != null;
    //@ requires moveIndex >= 0;
    //@ requires previousFullmoveNumber >= 1;
    //@ requires kingSide || queenSide;
    //@ requires !(kingSide && queenSide);
    public CastlingMove(Position from, Position to,
                        Color pieceColor, boolean kingSide, boolean queenSide,
                        CastlingRights previousCastlingRights,
                        int previousEnPassantRow, int previousEnPassantCol,
                        int previousFullmoveNumber,
                        int moveIndex, long timestamp, long timeRemaining,
                        String algebraicNotation, String resultingFEN)
    {
        super(from, to, "King", pieceColor,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
        
        this.kingSide = kingSide;
        this.queenSide = queenSide;
    }
    
    //@ requires fromRow >= 0;
    //@ requires fromCol >= 0;
    //@ requires toRow >= 0;
    //@ requires toCol >= 0;
    //@ requires moveIndex >= 0;
    //@ requires previousFullmoveNumber >= 1;
    //@ requires kingSide || queenSide;
    //@ requires !(kingSide && queenSide);
    public CastlingMove(int fromRow, int fromCol, int toRow, int toCol,
                        Color pieceColor, boolean kingSide, boolean queenSide,
                        CastlingRights previousCastlingRights,
                        int previousEnPassantRow, int previousEnPassantCol,
                        int previousFullmoveNumber,
                        int moveIndex, long timestamp, long timeRemaining,
                        String algebraicNotation, String resultingFEN)
    {
        this(new Position(fromRow, fromCol), new Position(toRow, toCol), pieceColor, kingSide, queenSide,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
    }
    
    //@ pure
    public boolean isCastleKingSide()
    {
        return kingSide;
    }
    
    //@ pure
    public boolean isCastleQueenSide()
    {
        return queenSide;
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isCapture()
    {
        return false;
    }
    
    //@ also
    //@ ensures \result == true;
    public boolean isCastle()
    {
        return true;
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isEnPassant()
    {
        return false;
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isPromotion()
    {
        return false;
    }
    
    public String toString()
    {
        if (!algebraicNotation.isEmpty())
        {
            return algebraicNotation;
        }
        
        StringBuilder sb = new StringBuilder();
        if (kingSide)
        {
            sb.append("O-O");
        }
        else
        {
            sb.append("O-O-O");
        }
        
        if (resultsInCheckmate)
        {
            sb.append("#");
        }
        else if (resultsInCheck)
        {
            sb.append("+");
        }
        
        return sb.toString();
    }
}
