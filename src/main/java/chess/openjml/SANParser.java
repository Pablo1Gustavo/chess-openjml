package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.Position;

/**
 * Parses Standard Algebraic Notation (SAN) and converts to board moves
 */
public class SANParser
{
    /**
     * Parse a SAN move and execute it on the game
     * Returns true if move was successful, false otherwise
     */
    //@ requires game != null;
    //@ requires san != null;
    public static boolean parseSANAndMove(Game game, String san)
    {
        san = san.trim().toLowerCase();
        
        // Handle castling
        if (san.equals("o-o"))
        {
            return handleCastling(game, true);
        }
        if (san.equals("o-o-o"))
        {
            return handleCastling(game, false);
        }
        
        // Remove check/checkmate markers
        san = san.replaceAll("[+#]$", "");
        
        // Check if it's a piece move first (k, q, r, b, n)
        if (san.length() > 0 && "kqrbn".indexOf(san.charAt(0)) >= 0)
        {
            return parsePieceMove(game, san);
        }
        
        // Try pawn move: e4, e8=Q, exd5, etc.
        if (Character.isLowerCase(san.charAt(0)))
        {
            return parsePawnMove(game, san);
        }
        
        return false;
    }
    
    //@ requires game != null;
    //@ requires san != null;
    private static boolean parsePawnMove(Game game, String san)
    {
        Board board = game.getBoard();
        Color player = game.getCurrentPlayer();
        
        // Check for promotion: e8=Q, exd8=Q, etc.
        String promotionPiece = null;
        if (san.contains("="))
        {
            String[] parts = san.split("=");
            san = parts[0];
            char promotionChar = parts[1].charAt(0);
            promotionPiece = switch (promotionChar)
            {
                case 'q' -> "Queen";
                case 'r' -> "Rook";
                case 'b' -> "Bishop";
                case 'n' -> "Knight";
                default -> null;
            };
        }
        
        // Pattern: [a-h]x[a-h][1-8] or [a-h][1-8]
        int toCol = san.charAt(san.length() - 2) - 'a';
        int toRow = Integer.parseInt(san.substring(san.length() - 1)) - 1;
        
        if (san.contains("x"))
        {
            // Capture
            int fromCol = san.charAt(0) - 'a';
            
            // Find pawn on fromCol that can capture to toCol/toRow
            int direction = player == Color.WHITE ? 1 : -1;
            for (int row = 0; row < 8; row++)
            {
                if (board.isCellOccupied(new Position(row, fromCol)))
                {
                    Optional<Piece> piece = board.getPieceAt(new Position(row, fromCol));
                    if (piece.isPresent() && piece.get().getColor() == player)
                    {
                        int expectedRow = toRow - direction;
                        if (row == expectedRow)
                        {
                            return game.movePiece(row, fromCol, toRow, toCol, promotionPiece);
                        }
                    }
                }
            }
        }
        else
        {
            // Regular pawn move: find pawn that can move to this square
            int direction = player == Color.WHITE ? 1 : -1;
            
            // Try one square back
            int fromRow = toRow - direction;
            if (board.isWithinBounds(new Position(fromRow, toCol)) && board.isCellOccupied(new Position(fromRow, toCol)))
            {
                Optional<Piece> piece = board.getPieceAt(new Position(fromRow, toCol));
                if (piece.isPresent() && piece.get().getColor() == player)
                {
                    return game.movePiece(fromRow, toCol, toRow, toCol, promotionPiece);
                }
            }
            
            // Try two squares back (initial pawn move)
            fromRow = toRow - 2 * direction;
            if (board.isWithinBounds(new Position(fromRow, toCol)) && board.isCellOccupied(new Position(fromRow, toCol)))
            {
                Optional<Piece> piece = board.getPieceAt(new Position(fromRow, toCol));
                if (piece.isPresent() && piece.get().getColor() == player)
                {
                    return game.movePiece(fromRow, toCol, toRow, toCol, promotionPiece);
                }
            }
        }
        
        return false;
    }
    
    //@ requires game != null;
    //@ requires san != null;
    private static boolean parsePieceMove(Game game, String san)
    {
        Board board = game.getBoard();
        Color player = game.getCurrentPlayer();
        
        char pieceChar = san.charAt(0);
        String pieceName = getPieceName(pieceChar);
        
        // Parse the destination square (always last 2 characters)
        int toCol = san.charAt(san.length() - 2) - 'a';
        int toRow = Integer.parseInt(san.substring(san.length() - 1)) - 1;
        
        // Check for capture (contains 'x')
        boolean isCapture = san.contains("x");
        
        // Parse disambiguation - everything between piece letter and destination (or 'x')
        // Examples: Nbd7 -> "b", N4d7 -> "4", Nb4d7 -> "b4", Nxd7 -> ""
        String disambiguation = "";
        int startIdx = 1; // After piece letter
        int endIdx = san.length() - 2; // Before destination square
        
        // If there's a capture 'x', disambiguation is before it
        if (isCapture)
        {
            int xPos = san.indexOf('x');
            endIdx = xPos;
        }
        
        if (endIdx > startIdx)
        {
            disambiguation = san.substring(startIdx, endIdx);
        }
        
        // Parse disambiguation into file and/or rank
        Integer disambigFile = null;
        Integer disambigRank = null;
        
        for (char c : disambiguation.toCharArray())
        {
            if (c >= 'a' && c <= 'h')
            {
                disambigFile = c - 'a';
            }
            else if (c >= '1' && c <= '8')
            {
                disambigRank = c - '1';
            }
        }
        
        // Find all pieces of the right type that can move to the destination
        for (int row = 0; row < 8; row++)
        {
            for (int col = 0; col < 8; col++)
            {
                if (board.isCellOccupied(new Position(row, col)))
                {
                    Optional<Piece> piece = board.getPieceAt(new Position(row, col));
                    if (piece.isPresent() && 
                        piece.get().getColor() == player &&
                        piece.get().getClass().getSimpleName().equals(pieceName))
                    {
                        // Check disambiguation constraints
                        if (disambigFile != null && col != disambigFile)
                        {
                            continue; // Wrong file
                        }
                        if (disambigRank != null && row != disambigRank)
                        {
                            continue; // Wrong rank
                        }
                        
                        // Check if this piece can make the move
                        if (piece.get().isValidMove(board, new Position(toRow, toCol)) &&
                            !game.wouldLeaveKingInCheck(row, col, toRow, toCol))
                        {
                            return game.movePiece(row, col, toRow, toCol);
                        }
                    }
                }
            }
        }
        
        return false;
    }
    
    //@ requires game != null;
    private static boolean handleCastling(Game game, boolean kingside)
    {
        return game.castle(kingside);
    }
    
    //@ ensures \result != null;
    //@ pure
    private static String getPieceName(char pieceChar)
    {
        return switch (pieceChar)
        {
            case 'k' -> "King";
            case 'q' -> "Queen";
            case 'r' -> "Rook";
            case 'b' -> "Bishop";
            case 'n' -> "Knight";
            default -> "";
        };
    }
}
