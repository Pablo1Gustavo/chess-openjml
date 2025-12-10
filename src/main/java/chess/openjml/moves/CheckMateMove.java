package chess.openjml.moves;

import chess.openjml.pieces.Piece;
import java.util.regex.Pattern;

//@ non_null_by_default
public class CheckMateMove extends BaseMove
{
    //@ private static invariant CHECKMATE_SUFFIX != null;
    private static final Pattern CHECKMATE_SUFFIX = Pattern.compile("#$");
    //@ spec_public
    protected final BaseMove baseMove;

    //@ requires baseMove != null;
    //@ ensures this.baseMove == baseMove;
    public CheckMateMove(BaseMove baseMove)
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
