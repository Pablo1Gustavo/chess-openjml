package chess.openjml.pieces.enums;

public enum Color
{
    BLACK,
    WHITE;
    
    //@ ensures this == WHITE ==> \result == 1;
    //@ ensures this == BLACK ==> \result == -1;
    //@ pure
    public int direction()
    {
        return this == WHITE ? 1 : -1;
    }
}
