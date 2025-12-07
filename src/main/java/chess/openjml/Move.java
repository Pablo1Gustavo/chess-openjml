package chess.openjml;

import chess.openjml.pieces.enums.Color;

/**
 * Chess move with complete information for reconstruction, undo, and history tracking.
 */
public class Move
{
    // Basic move information
    //@ spec_public
    private final int fromRow;
    //@ spec_public
    private final int fromCol;
    //@ spec_public
    private final int toRow;
    //@ spec_public
    private final int toCol;
    //@ spec_public
    private final String pieceType;
    //@ spec_public
    private final Color pieceColor;
    
    // Captures and promotions
    //@ spec_public
    private final String capturedPieceType;
    //@ spec_public
    private final int capturedRow;
    //@ spec_public
    private final int capturedCol;
    //@ spec_public
    private final String promotionPieceType;
    
    // Move type flags
    //@ spec_public
    private final boolean isCapture;
    //@ spec_public
    private final boolean isCastleKingSide;
    //@ spec_public
    private final boolean isCastleQueenSide;
    //@ spec_public
    private final boolean isEnPassant;
    //@ spec_public
    private final boolean isPromotion;
    //@ spec_public
    private boolean resultsInCheck;
    //@ spec_public
    private boolean resultsInCheckmate;
    
    // Previous state (for undo)
    //@ spec_public
    private final CastlingRights previousCastlingRights;
    //@ spec_public
    private final int previousEnPassantRow;
    //@ spec_public
    private final int previousEnPassantCol;
    //@ spec_public
    private final int previousHalfmoveClock;
    //@ spec_public
    private final int previousFullmoveNumber;
    
    // History metadata
    //@ spec_public
    private final int moveIndex;
    //@ spec_public
    private final long timestamp;
    //@ spec_public
    private final long timeRemaining;
    
    // Notation representations
    //@ spec_public
    private String algebraicNotation;
    //@ spec_public
    private String resultingFEN;
    
    //@ public invariant fromRow >= 0 && fromRow < 8;
    //@ public invariant fromCol >= 0 && fromCol < 8;
    //@ public invariant toRow >= 0 && toRow < 8;
    //@ public invariant toCol >= 0 && toCol < 8;
    //@ public invariant pieceType != null;
    //@ public invariant pieceColor != null;
    //@ public invariant moveIndex >= 0;
    //@ public invariant previousFullmoveNumber >= 1;
    //@ public invariant previousHalfmoveClock >= 0;
    //@ public invariant resultsInCheckmate ==> resultsInCheck;
    
    //@ requires builder != null;
    private Move(Builder builder)
    {
        this.fromRow = builder.fromRow;
        this.fromCol = builder.fromCol;
        this.toRow = builder.toRow;
        this.toCol = builder.toCol;
        this.pieceType = builder.pieceType;
        this.pieceColor = builder.pieceColor;
        
        this.capturedPieceType = builder.capturedPieceType;
        this.capturedRow = builder.capturedRow;
        this.capturedCol = builder.capturedCol;
        this.promotionPieceType = builder.promotionPieceType;
        
        this.isCapture = builder.isCapture;
        this.isCastleKingSide = builder.isCastleKingSide;
        this.isCastleQueenSide = builder.isCastleQueenSide;
        this.isEnPassant = builder.isEnPassant;
        this.isPromotion = builder.isPromotion;
        this.resultsInCheck = builder.resultsInCheck;
        this.resultsInCheckmate = builder.resultsInCheckmate;
        
        this.previousCastlingRights = builder.previousCastlingRights;
        this.previousEnPassantRow = builder.previousEnPassantRow;
        this.previousEnPassantCol = builder.previousEnPassantCol;
        this.previousHalfmoveClock = builder.previousHalfmoveClock;
        this.previousFullmoveNumber = builder.previousFullmoveNumber;
        
        this.moveIndex = builder.moveIndex;
        this.timestamp = builder.timestamp;
        this.timeRemaining = builder.timeRemaining;
        
        this.algebraicNotation = builder.algebraicNotation;
        this.resultingFEN = builder.resultingFEN;
    }
    
    // Getters
    
    //@ ensures \result == fromRow;
    //@ pure
    public int getFromRow() { return fromRow; }
    //@ ensures \result == fromCol;
    //@ pure
    public int getFromCol() { return fromCol; }
    //@ ensures \result == toRow;
    //@ pure
    public int getToRow() { return toRow; }
    //@ ensures \result == toCol;
    //@ pure
    public int getToCol() { return toCol; }
    //@ ensures \result == pieceType;
    //@ pure
    public String getPieceType() { return pieceType; }
    //@ ensures \result == pieceColor;
    //@ pure
    public Color getPieceColor() { return pieceColor; }
    
    //@ pure
    public String getCapturedPieceType() { return capturedPieceType; }
    //@ pure
    public int getCapturedRow() { return capturedRow; }
    //@ pure
    public int getCapturedCol() { return capturedCol; }
    //@ pure
    public String getPromotionPieceType() { return promotionPieceType; }
    
    //@ pure
    public boolean isCapture() { return isCapture; }
    //@ pure
    public boolean isCastleKingSide() { return isCastleKingSide; }
    //@ pure
    public boolean isCastleQueenSide() { return isCastleQueenSide; }
    //@ pure
    public boolean isCastle() { return isCastleKingSide || isCastleQueenSide; }
    //@ pure
    public boolean isEnPassant() { return isEnPassant; }
    //@ pure
    public boolean isPromotion() { return isPromotion; }
    //@ pure
    public boolean resultsInCheck() { return resultsInCheck; }
    //@ pure
    public boolean resultsInCheckmate() { return resultsInCheckmate; }
    
    //@ pure
    public CastlingRights getPreviousCastlingRights() { return previousCastlingRights; }
    //@ pure
    public int getPreviousEnPassantRow() { return previousEnPassantRow; }
    //@ pure
    public int getPreviousEnPassantCol() { return previousEnPassantCol; }
    //@ pure
    public int getPreviousHalfmoveClock() { return previousHalfmoveClock; }
    //@ pure
    public int getPreviousFullmoveNumber() { return previousFullmoveNumber; }
    
    //@ ensures \result >= 0;
    //@ pure
    public int getMoveIndex() { return moveIndex; }
    //@ pure
    public long getTimestamp() { return timestamp; }
    //@ pure
    public long getTimeRemaining() { return timeRemaining; }
    
    //@ pure
    public String getAlgebraicNotation() { return algebraicNotation; }
    //@ pure
    public String getResultingFEN() { return resultingFEN; }
    
    //@ ensures resultsInCheck == check;
    public void setResultsInCheck(boolean check) { this.resultsInCheck = check; }
    //@ ensures resultsInCheckmate == checkmate;
    //@ ensures checkmate ==> resultsInCheck;
    public void setResultsInCheckmate(boolean checkmate) { this.resultsInCheckmate = checkmate; }
    //@ requires notation != null;
    //@ ensures algebraicNotation == notation;
    public void setAlgebraicNotation(String notation) { this.algebraicNotation = notation; }
    //@ requires fen != null;
    //@ ensures resultingFEN == fen;
    public void setResultingFEN(String fen) { this.resultingFEN = fen; }
    
    // Utility methods
    
    //@ ensures \result != null;
    //@ ensures \result.length() == 2;
    //@ pure
    public String getFromSquare()
    {
        return squareToAlgebraic(fromRow, fromCol);
    }
    
    //@ ensures \result != null;
    //@ ensures \result.length() == 2;
    //@ pure
    public String getToSquare()
    {
        return squareToAlgebraic(toRow, toCol);
    }
    
    //@ pure
    public String getCapturedSquare()
    {
        if (!isCapture) return null;
        return squareToAlgebraic(capturedRow, capturedCol);
    }
    
    //@ requires row >= 0 && row < 8;
    //@ requires col >= 0 && col < 8;
    //@ ensures \result != null;
    //@ ensures \result.length() == 2;
    //@ pure
    private String squareToAlgebraic(int row, int col)
    {
        if (row < 0 || col < 0) return null;
        char file = (char) ('a' + col);
        int rank = row + 1;
        return "" + file + rank;
    }
    
    //@ also ensures \result != null;
    //@ pure
    @Override
    public String toString()
    {
        if (algebraicNotation != null && !algebraicNotation.isEmpty())
        {
            return algebraicNotation;
        }
        
        String result = pieceType.charAt(0) + getFromSquare() + 
                       (isCapture ? "x" : "-") + getToSquare();
        
        if (isPromotion)
        {
            result += "=" + promotionPieceType.charAt(0);
        }
        
        if (resultsInCheckmate)
        {
            result += "#";
        }
        else if (resultsInCheck)
        {
            result += "+";
        }
        
        return result;
    }
    
    // Builder pattern
    
    public static class Builder
    {
        // Required
        //@ spec_public
        private int fromRow;
        //@ spec_public
        private int fromCol;
        //@ spec_public
        private int toRow;
        //@ spec_public
        private int toCol;
        //@ spec_public
        private String pieceType;
        //@ spec_public
        private Color pieceColor;
        
        // Optional with defaults
        //@ spec_public
        private String capturedPieceType = null;
        //@ spec_public
        private int capturedRow = -1;
        //@ spec_public
        private int capturedCol = -1;
        //@ spec_public
        private String promotionPieceType = null;
        
        //@ spec_public
        private boolean isCapture = false;
        //@ spec_public
        private boolean isCastleKingSide = false;
        //@ spec_public
        private boolean isCastleQueenSide = false;
        //@ spec_public
        private boolean isEnPassant = false;
        //@ spec_public
        private boolean isPromotion = false;
        //@ spec_public
        private boolean resultsInCheck = false;
        //@ spec_public
        private boolean resultsInCheckmate = false;
        
        //@ spec_public
        private CastlingRights previousCastlingRights = new CastlingRights();
        //@ spec_public
        private int previousEnPassantRow = -1;
        //@ spec_public
        private int previousEnPassantCol = -1;
        //@ spec_public
        private int previousHalfmoveClock = 0;
        //@ spec_public
        private int previousFullmoveNumber = 1;
        
        //@ spec_public
        private int moveIndex = 0;
        //@ spec_public
        private long timestamp = System.currentTimeMillis();
        //@ spec_public
        private long timeRemaining = -1;
        
        //@ spec_public
        private String algebraicNotation = "";
        //@ spec_public
        private String resultingFEN = "";
        
        //@ requires fromRow >= 0 && fromRow < 8;
        //@ requires fromCol >= 0 && fromCol < 8;
        //@ requires toRow >= 0 && toRow < 8;
        //@ requires toCol >= 0 && toCol < 8;
        //@ requires pieceType != null;
        //@ requires pieceColor != null;
        public Builder(int fromRow, int fromCol, int toRow, int toCol, String pieceType, Color pieceColor)
        {
            this.fromRow = fromRow;
            this.fromCol = fromCol;
            this.toRow = toRow;
            this.toCol = toCol;
            this.pieceType = pieceType;
            this.pieceColor = pieceColor;
        }
        
        //@ requires capturedType != null;
        //@ requires capturedRow >= 0 && capturedRow < 8;
        //@ requires capturedCol >= 0 && capturedCol < 8;
        //@ ensures \result == this;
        public Builder capture(String capturedType, int capturedRow, int capturedCol)
        {
            this.isCapture = true;
            this.capturedPieceType = capturedType;
            this.capturedRow = capturedRow;
            this.capturedCol = capturedCol;
            return this;
        }
        
        //@ requires promotionType != null;
        //@ ensures \result == this;
        public Builder promotion(String promotionType)
        {
            this.isPromotion = true;
            this.promotionPieceType = promotionType;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder castleKingSide()
        {
            this.isCastleKingSide = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder castleQueenSide()
        {
            this.isCastleQueenSide = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder enPassant()
        {
            this.isEnPassant = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder check()
        {
            this.resultsInCheck = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder checkmate()
        {
            this.resultsInCheckmate = true;
            this.resultsInCheck = true;
            return this;
        }
        
        //@ requires castlingRights != null;
        //@ requires halfmoveClock >= 0;
        //@ requires fullmoveNumber >= 1;
        //@ ensures \result == this;
        public Builder previousState(CastlingRights castlingRights, int enPassantRow, int enPassantCol, 
                                    int halfmoveClock, int fullmoveNumber)
        {
            this.previousCastlingRights = castlingRights;
            this.previousEnPassantRow = enPassantRow;
            this.previousEnPassantCol = enPassantCol;
            this.previousHalfmoveClock = halfmoveClock;
            this.previousFullmoveNumber = fullmoveNumber;
            return this;
        }
        
        //@ requires index >= 0;
        //@ ensures \result == this;
        public Builder moveIndex(int index)
        {
            this.moveIndex = index;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder timestamp(long timestamp)
        {
            this.timestamp = timestamp;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder timeRemaining(long timeRemaining)
        {
            this.timeRemaining = timeRemaining;
            return this;
        }
        
        //@ requires notation != null;
        //@ ensures \result == this;
        public Builder algebraicNotation(String notation)
        {
            this.algebraicNotation = notation;
            return this;
        }
        
        //@ requires fen != null;
        //@ ensures \result == this;
        public Builder resultingFEN(String fen)
        {
            this.resultingFEN = fen;
            return this;
        }
        
        //@ ensures \result != null;
        public Move build()
        {
            return new Move(this);
        }
    }
    
    // Castling rights tracking
    
    public static class CastlingRights
    {
        private boolean whiteKingSide;
        private boolean whiteQueenSide;
        private boolean blackKingSide;
        private boolean blackQueenSide;
        
        public CastlingRights()
        {
            this.whiteKingSide = true;
            this.whiteQueenSide = true;
            this.blackKingSide = true;
            this.blackQueenSide = true;
        }
        
        public CastlingRights(boolean whiteKingSide, boolean whiteQueenSide, 
                             boolean blackKingSide, boolean blackQueenSide)
        {
            this.whiteKingSide = whiteKingSide;
            this.whiteQueenSide = whiteQueenSide;
            this.blackKingSide = blackKingSide;
            this.blackQueenSide = blackQueenSide;
        }
        
        // Copy constructor
        public CastlingRights(CastlingRights other)
        {
            this.whiteKingSide = other.whiteKingSide;
            this.whiteQueenSide = other.whiteQueenSide;
            this.blackKingSide = other.blackKingSide;
            this.blackQueenSide = other.blackQueenSide;
        }
        
        public boolean canWhiteCastleKingSide() { return whiteKingSide; }
        public boolean canWhiteCastleQueenSide() { return whiteQueenSide; }
        public boolean canBlackCastleKingSide() { return blackKingSide; }
        public boolean canBlackCastleQueenSide() { return blackQueenSide; }
        
        public void setWhiteKingSide(boolean value) { this.whiteKingSide = value; }
        public void setWhiteQueenSide(boolean value) { this.whiteQueenSide = value; }
        public void setBlackKingSide(boolean value) { this.blackKingSide = value; }
        public void setBlackQueenSide(boolean value) { this.blackQueenSide = value; }
        
        @Override
        public String toString()
        {
            StringBuilder sb = new StringBuilder();
            if (whiteKingSide) sb.append("K");
            if (whiteQueenSide) sb.append("Q");
            if (blackKingSide) sb.append("k");
            if (blackQueenSide) sb.append("q");
            return sb.length() > 0 ? sb.toString() : "-";
        }
    }
}
