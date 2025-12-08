package chess.openjml.moves;

import chess.openjml.pieces.enums.Color;

/**
 * Represents a standard chess move without special rules.
 * Does not involve captures, castling, en passant, or promotion.
 */
public class StandardMove extends BaseMove
{
    //@ requires from != null;
    //@ requires to != null;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    public StandardMove(Position from, Position to,
                        String pieceType, Color pieceColor,
                        CastlingRights previousCastlingRights,
                        int previousEnPassantRow, int previousEnPassantCol,
                        int previousHalfmoveClock, int previousFullmoveNumber,
                        int moveIndex, long timestamp, long timeRemaining,
                        String algebraicNotation, String resultingFEN)
    {
        super(from, to, pieceType, pieceColor,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousHalfmoveClock, previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
    }
    
    //@ requires fromRow >= 0;
    //@ requires fromCol >= 0;
    //@ requires toRow >= 0;
    //@ requires toCol >= 0;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    public StandardMove(int fromRow, int fromCol, int toRow, int toCol,
                        String pieceType, Color pieceColor,
                        CastlingRights previousCastlingRights,
                        int previousEnPassantRow, int previousEnPassantCol,
                        int previousHalfmoveClock, int previousFullmoveNumber,
                        int moveIndex, long timestamp, long timeRemaining,
                        String algebraicNotation, String resultingFEN)
    {
        this(new Position(fromRow, fromCol), new Position(toRow, toCol), pieceType, pieceColor,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousHalfmoveClock, previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isCapture()
    {
        return false;
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isCastle()
    {
        return false;
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
        sb.append(pieceType.charAt(0))
          .append(getFromSquare())
          .append('-')
          .append(getToSquare());
        
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
