package chess.openjml.moves;

import chess.openjml.pieces.enums.Color;

/**
 * Represents a pawn promotion move.
 * Can also be a capture-promotion (combining both properties).
 */
//@ non_null_by_default
public class PromotionMove extends BaseMove
{
    //@ spec_public
    private final String promotionPieceType;
    //@ spec_public
    private final String capturedPieceType;
    //@ spec_public
    private final Position capturedPosition;
    //@ spec_public
    private final boolean isAlsoCapture;
    
    //@ requires from != null;
    //@ requires to != null;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    public PromotionMove(Position from, Position to,
                         Color pieceColor, String promotionPieceType,
                         String capturedPieceType, Position capturedPosition,
                         CastlingRights previousCastlingRights,
                         int previousEnPassantRow, int previousEnPassantCol,
                         int previousHalfmoveClock, int previousFullmoveNumber,
                         int moveIndex, long timestamp, long timeRemaining,
                         String algebraicNotation, String resultingFEN)
    {
        super(from, to, "Pawn", pieceColor,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousHalfmoveClock, previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
        
        this.promotionPieceType = promotionPieceType;
        this.capturedPieceType = capturedPieceType;
        this.capturedPosition = capturedPosition;
        this.isAlsoCapture = !capturedPieceType.isEmpty();
    }
    
    //@ requires fromRow >= 0;
    //@ requires fromCol >= 0;
    //@ requires toRow >= 0;
    //@ requires toCol >= 0;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    public PromotionMove(int fromRow, int fromCol, int toRow, int toCol,
                         Color pieceColor, String promotionPieceType,
                         String capturedPieceType, int capturedRow, int capturedCol,
                         CastlingRights previousCastlingRights,
                         int previousEnPassantRow, int previousEnPassantCol,
                         int previousHalfmoveClock, int previousFullmoveNumber,
                         int moveIndex, long timestamp, long timeRemaining,
                         String algebraicNotation, String resultingFEN)
    {
        this(new Position(fromRow, fromCol), new Position(toRow, toCol),
              pieceColor, promotionPieceType, capturedPieceType,
              capturedRow >= 0 ? new Position(capturedRow, capturedCol) : null,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousHalfmoveClock, previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
    }
    
    //@ pure
    public String getPromotionPieceType()
    {
        return promotionPieceType;
    }
    
    //@ pure
    public String getCapturedPieceType()
    {
        return capturedPieceType;
    }
    
    //@ pure
    public Position getCapturedPosition()
    {
        return capturedPosition;
    }
    
    //@ pure
    public int getCapturedRow()
    {
        return capturedPosition != null ? capturedPosition.getRow() : -1;
    }
    
    //@ pure
    public int getCapturedCol()
    {
        return capturedPosition != null ? capturedPosition.getCol() : -1;
    }
    
    //@ requires isCapture();
    //@ pure
    public String getCapturedSquare()
    {
        return capturedPosition != null ? capturedPosition.toAlgebraic() : "";
    }
    
    public boolean isCapture()
    {
        return isAlsoCapture;
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
    //@ ensures \result == true;
    public boolean isPromotion()
    {
        return true;
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
          .append(isAlsoCapture ? 'x' : '-')
          .append(getToSquare())
          .append("=")
          .append(promotionPieceType.charAt(0));
        
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
