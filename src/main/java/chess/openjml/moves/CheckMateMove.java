package chess.openjml.moves;

import chess.openjml.pieces.Piece;

public class CheckMateMove<T extends Piece> extends BaseMove<T>
{
    protected final BaseMove<T> baseMove;

    public CheckMateMove(BaseMove<T> baseMove)
    {
        super(baseMove.movePair, baseMove.pieceType, baseMove.disambiguationType);
        this.baseMove = baseMove;
    }

    @Override
    public String algebraicNotation()
    {
        return baseMove.algebraicNotation() + "#";
    }
}
