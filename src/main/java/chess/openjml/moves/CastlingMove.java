package chess.openjml.moves;

import chess.openjml.pieces.King;

public class CastlingMove extends BaseMove<King>
{
    protected final boolean isKingSide;

    public CastlingMove(MovePair movePair, boolean isKingSide)
    {
        super(movePair, King.class, DisambiguationType.NONE);
        this.isKingSide = isKingSide;
    }

    @Override
    public String algebraicNotation()
    {
        return isKingSide ? "O-O" : "O-O-O";
    }
}
