package chess.openjml.moves;

import java.util.regex.Pattern;

//@ non_null_by_default
public class MovePair
{
    //@ public static invariant SIMPLE_FROM_TO_NOTATION != null;
    public static final Pattern SIMPLE_FROM_TO_NOTATION = Pattern.compile("^[a-z]\\d+ [a-z]\\d+$");

    public final Position from;
    public final Position to;
    
    //@ requires from != null && to != null;
    //@ requires !from.equals(to);
    //@ ensures this.from == from;
    //@ ensures this.to == to;
    public MovePair(Position from, Position to)
    {
        this.from = from;
        this.to = to;
    }

    //@ requires notation != null;
    //@ pure
    public static MovePair fromString(String notation)
    {
        String[] parts = notation.split(" ");

        var from = Position.fromAlgebraic(parts[0]);
        var to = Position.fromAlgebraic(parts[1]);

        return new MovePair(from, to);
    }

    //@ ensures \result == from;
    //@ pure
    public Position getFrom()
    {
        return from;
    }

    public Position getTo()
    {
        return to;
    }
}
