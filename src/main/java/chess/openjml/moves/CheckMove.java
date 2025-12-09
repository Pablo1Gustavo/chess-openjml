package chess.openjml.moves;

import chess.openjml.pieces.Piece;

public class CheckMove<T extends Piece> extends BaseMove<T>
{
    protected final BaseMove<T> baseMove;

    public CheckMove(BaseMove<T> baseMove)
    {
        super(baseMove.movePair, baseMove.pieceType, baseMove.disambiguationType);
        this.baseMove = baseMove;
    }

    @Override
    public String algebraicNotation()
    {
        return baseMove.algebraicNotation() + "+";
    }
}
