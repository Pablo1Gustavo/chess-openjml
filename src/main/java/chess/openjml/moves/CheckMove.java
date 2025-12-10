package chess.openjml.moves;

import chess.openjml.pieces.Piece;
import java.util.regex.Pattern;

public class CheckMove extends BaseMove
{
    private static final Pattern CHECK_SUFFIX = Pattern.compile("\\+$");

    protected final BaseMove baseMove;

    public CheckMove(BaseMove baseMove)
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
