package chess.openjml.moves;

/**
 * Represents castling rights for both players.
 */
//@ non_null_by_default
public class CastlingRights
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
    
    public CastlingRights(CastlingRights other)
    {
        this.whiteKingSide = other.whiteKingSide;
        this.whiteQueenSide = other.whiteQueenSide;
        this.blackKingSide = other.blackKingSide;
        this.blackQueenSide = other.blackQueenSide;
    }
    
    public boolean canWhiteCastleKingSide()
    {
        return whiteKingSide;
    }
    public boolean canWhiteCastleQueenSide()
    {
        return whiteQueenSide;
    }
    public boolean canBlackCastleKingSide()
    {
        return blackKingSide;
    }
    public boolean canBlackCastleQueenSide()
    {
        return blackQueenSide;
    }
    
    public void setWhiteKingSide(boolean value)
    {
        this.whiteKingSide = value;
    }
    public void setWhiteQueenSide(boolean value)
    {
        this.whiteQueenSide = value;
    }
    public void setBlackKingSide(boolean value)
    {
        this.blackKingSide = value;
    }
    public void setBlackQueenSide(boolean value)
    {
        this.blackQueenSide = value;
    }
    
    @Override
    public String toString()
    {
        StringBuilder sb = new StringBuilder();
        if (whiteKingSide)
        {
            sb.append("K");
        }
        if (whiteQueenSide)
        {
            sb.append("Q");
        }
        if (blackKingSide)
        {
            sb.append("k");
        }
        if (blackQueenSide)
        {
            sb.append("q");
        }

        return sb.isEmpty()
            ? "-"
            : sb.toString();
    }
}
