package chess.openjml;

import chess.openjml.pieces.enums.Color;

/**
 * Chess move with complete information for reconstruction, undo, and history tracking.
 */
public class Move
{
    // Basic move information
    private final int fromRow;
    private final int fromCol;
    private final int toRow;
    private final int toCol;
    private final String pieceType;
    private final Color pieceColor;
    
    // Captures and promotions
    private final String capturedPieceType;
    private final int capturedRow;
    private final int capturedCol;
    private final String promotionPieceType;
    
    // Move type flags
    private final boolean isCapture;
    private final boolean isCastleKingSide;
    private final boolean isCastleQueenSide;
    private final boolean isEnPassant;
    private final boolean isPromotion;
    private boolean resultsInCheck;
    private boolean resultsInCheckmate;
    
    // Previous state (for undo)
    private final CastlingRights previousCastlingRights;
    private final int previousEnPassantRow;
    private final int previousEnPassantCol;
    private final int previousHalfmoveClock;
    private final int previousFullmoveNumber;
    
    // History metadata
    private final int moveIndex;
    private final long timestamp;
    private final long timeRemaining;
    
    // Notation representations
    private String algebraicNotation;
    private String resultingFEN;
    
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
    
    public int getFromRow() { return fromRow; }
    public int getFromCol() { return fromCol; }
    public int getToRow() { return toRow; }
    public int getToCol() { return toCol; }
    public String getPieceType() { return pieceType; }
    public Color getPieceColor() { return pieceColor; }
    
    public String getCapturedPieceType() { return capturedPieceType; }
    public int getCapturedRow() { return capturedRow; }
    public int getCapturedCol() { return capturedCol; }
    public String getPromotionPieceType() { return promotionPieceType; }
    
    public boolean isCapture() { return isCapture; }
    public boolean isCastleKingSide() { return isCastleKingSide; }
    public boolean isCastleQueenSide() { return isCastleQueenSide; }
    public boolean isCastle() { return isCastleKingSide || isCastleQueenSide; }
    public boolean isEnPassant() { return isEnPassant; }
    public boolean isPromotion() { return isPromotion; }
    public boolean resultsInCheck() { return resultsInCheck; }
    public boolean resultsInCheckmate() { return resultsInCheckmate; }
    
    public CastlingRights getPreviousCastlingRights() { return previousCastlingRights; }
    public int getPreviousEnPassantRow() { return previousEnPassantRow; }
    public int getPreviousEnPassantCol() { return previousEnPassantCol; }
    public int getPreviousHalfmoveClock() { return previousHalfmoveClock; }
    public int getPreviousFullmoveNumber() { return previousFullmoveNumber; }
    
    public int getMoveIndex() { return moveIndex; }
    public long getTimestamp() { return timestamp; }
    public long getTimeRemaining() { return timeRemaining; }
    
    public String getAlgebraicNotation() { return algebraicNotation; }
    public String getResultingFEN() { return resultingFEN; }
    
    public void setResultsInCheck(boolean check) { this.resultsInCheck = check; }
    public void setResultsInCheckmate(boolean checkmate) { this.resultsInCheckmate = checkmate; }
    public void setAlgebraicNotation(String notation) { this.algebraicNotation = notation; }
    public void setResultingFEN(String fen) { this.resultingFEN = fen; }
    
    // Utility methods
    
    public String getFromSquare()
    {
        return squareToAlgebraic(fromRow, fromCol);
    }
    
    public String getToSquare()
    {
        return squareToAlgebraic(toRow, toCol);
    }
    
    public String getCapturedSquare()
    {
        if (!isCapture) return null;
        return squareToAlgebraic(capturedRow, capturedCol);
    }
    
    private String squareToAlgebraic(int row, int col)
    {
        if (row < 0 || col < 0) return null;
        char file = (char) ('a' + col);
        int rank = row + 1;
        return "" + file + rank;
    }
    
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
        private int fromRow;
        private int fromCol;
        private int toRow;
        private int toCol;
        private String pieceType;
        private Color pieceColor;
        
        // Optional with defaults
        private String capturedPieceType = null;
        private int capturedRow = -1;
        private int capturedCol = -1;
        private String promotionPieceType = null;
        
        private boolean isCapture = false;
        private boolean isCastleKingSide = false;
        private boolean isCastleQueenSide = false;
        private boolean isEnPassant = false;
        private boolean isPromotion = false;
        private boolean resultsInCheck = false;
        private boolean resultsInCheckmate = false;
        
        private CastlingRights previousCastlingRights = new CastlingRights();
        private int previousEnPassantRow = -1;
        private int previousEnPassantCol = -1;
        private int previousHalfmoveClock = 0;
        private int previousFullmoveNumber = 1;
        
        private int moveIndex = 0;
        private long timestamp = System.currentTimeMillis();
        private long timeRemaining = -1;
        
        private String algebraicNotation = "";
        private String resultingFEN = "";
        
        public Builder(int fromRow, int fromCol, int toRow, int toCol, String pieceType, Color pieceColor)
        {
            this.fromRow = fromRow;
            this.fromCol = fromCol;
            this.toRow = toRow;
            this.toCol = toCol;
            this.pieceType = pieceType;
            this.pieceColor = pieceColor;
        }
        
        public Builder capture(String capturedType, int capturedRow, int capturedCol)
        {
            this.isCapture = true;
            this.capturedPieceType = capturedType;
            this.capturedRow = capturedRow;
            this.capturedCol = capturedCol;
            return this;
        }
        
        public Builder promotion(String promotionType)
        {
            this.isPromotion = true;
            this.promotionPieceType = promotionType;
            return this;
        }
        
        public Builder castleKingSide()
        {
            this.isCastleKingSide = true;
            return this;
        }
        
        public Builder castleQueenSide()
        {
            this.isCastleQueenSide = true;
            return this;
        }
        
        public Builder enPassant()
        {
            this.isEnPassant = true;
            return this;
        }
        
        public Builder check()
        {
            this.resultsInCheck = true;
            return this;
        }
        
        public Builder checkmate()
        {
            this.resultsInCheckmate = true;
            this.resultsInCheck = true;
            return this;
        }
        
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
        
        public Builder moveIndex(int index)
        {
            this.moveIndex = index;
            return this;
        }
        
        public Builder timestamp(long timestamp)
        {
            this.timestamp = timestamp;
            return this;
        }
        
        public Builder timeRemaining(long timeRemaining)
        {
            this.timeRemaining = timeRemaining;
            return this;
        }
        
        public Builder algebraicNotation(String notation)
        {
            this.algebraicNotation = notation;
            return this;
        }
        
        public Builder resultingFEN(String fen)
        {
            this.resultingFEN = fen;
            return this;
        }
        
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
