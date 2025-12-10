package chess.openjml.moves;

import chess.openjml.pieces.Pawn;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.King;
import java.util.regex.Pattern;

//@ non_null_by_default
public class CaptureMove extends BaseMove
{
    public static final Pattern CAPTURE_MOVE = Pattern.compile("^([kqrbn])?([a-z])?([\\d])?x([a-z]\\d+)$");
    //@ spec_public
    protected final Class<? extends Piece> capturedPieceType;

    //@ requires movePair != null && pieceType != null && capturedPieceType != null && disambiguationType != null;
    //@ requires capturedPieceType != King.class;
    //@ ensures this.capturedPieceType == capturedPieceType;
    public CaptureMove(MovePair movePair, Class<? extends Piece> pieceType, Class<? extends Piece> capturedPieceType, DisambiguationType disambiguationType)
    {
        super(movePair, pieceType, disambiguationType);
        this.capturedPieceType = capturedPieceType;
    }

    public CaptureMove(MovePair movePair, Class<? extends Piece> pieceType, Class<? extends Piece> capturedPieceType)
    {
        this(movePair, pieceType, capturedPieceType, DisambiguationType.NONE);
    }

    @Override
    public String algebraicNotation()
    {        
        if (pieceType == Pawn.class)
        {
            return movePair.getFrom().getColChar() + "x" + movePair.getTo().toAlgebraic();
        }
        return getPieceAlgebraicNotation(pieceType) + disambiguationAlgebraicNotation() + "x" + movePair.getTo().toAlgebraic();
    }
}
