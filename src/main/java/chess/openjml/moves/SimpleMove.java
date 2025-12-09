package chess.openjml.moves;

import chess.openjml.pieces.Piece;

public class SimpleMove<T extends Piece> extends BaseMove<T>
{    
    public SimpleMove(MovePair movePair, Class<T> pieceType, DisambiguationType disambiguationType)
    {
        super(movePair, pieceType, disambiguationType);
    }

    public SimpleMove(MovePair movePair, Class<T> pieceType)
    {
        this(movePair, pieceType, DisambiguationType.NONE);
    }

    @Override
    public String algebraicNotation()
    {
        return getPieceAlgebraicNotation(pieceType) + disambiguationAlgebraicNotation() + movePair.getTo().toAlgebraic();
    }
}
