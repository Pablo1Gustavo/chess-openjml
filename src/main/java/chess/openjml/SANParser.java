package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;

/**
 * Parses Standard Algebraic Notation (SAN) and converts to board moves
 */
public class SANParser
{
    /**
     * Parse a SAN move and execute it on the game
     * Returns true if move was successful, false otherwise
     */
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
    
    private static boolean parsePawnMove(Game game, String san)
    {
        Board board = game.getBoard();
        Color player = game.getCurrentPlayer();
        
        // Pattern: [a-h]x[a-h][1-8] or [a-h][1-8] or [a-h]x[a-h][1-8]=X
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
                if (board.isCellOccupied(row, fromCol))
                {
                    Optional<Piece> piece = board.getPieceAt(row, fromCol);
                    if (piece.isPresent() && piece.get().getColor() == player)
                    {
                        int expectedRow = toRow - direction;
                        if (row == expectedRow)
                        {
                            return game.movePiece(row, fromCol, toRow, toCol);
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
            if (board.isWithinBounds(fromRow, toCol) && board.isCellOccupied(fromRow, toCol))
            {
                Optional<Piece> piece = board.getPieceAt(fromRow, toCol);
                if (piece.isPresent() && piece.get().getColor() == player)
                {
                    return game.movePiece(fromRow, toCol, toRow, toCol);
                }
            }
            
            // Try two squares back (initial pawn move)
            fromRow = toRow - 2 * direction;
            if (board.isWithinBounds(fromRow, toCol) && board.isCellOccupied(fromRow, toCol))
            {
                Optional<Piece> piece = board.getPieceAt(fromRow, toCol);
                if (piece.isPresent() && piece.get().getColor() == player)
                {
                    return game.movePiece(fromRow, toCol, toRow, toCol);
                }
            }
        }
        
        return false;
    }
    
    private static boolean parsePieceMove(Game game, String san)
    {
        Board board = game.getBoard();
        Color player = game.getCurrentPlayer();
        
        char pieceChar = san.charAt(0);
        String pieceName = getPieceName(pieceChar);
        
        int toCol = san.charAt(san.length() - 2) - 'a';
        int toRow = Integer.parseInt(san.substring(san.length() - 1)) - 1;
        
        // Try to find a piece of the right type that can move there
        for (int row = 0; row < 8; row++)
        {
            for (int col = 0; col < 8; col++)
            {
                if (board.isCellOccupied(row, col))
                {
                    Optional<Piece> piece = board.getPieceAt(row, col);
                    if (piece.isPresent() && 
                        piece.get().getColor() == player &&
                        piece.get().getClass().getSimpleName().equals(pieceName) &&
                        piece.get().isValidMove(board, toRow, toCol))
                    {
                        return game.movePiece(row, col, toRow, toCol);
                    }
                }
            }
        }
        
        return false;
    }
    
    private static boolean handleCastling(Game game, boolean kingside)
    {
        Board board = game.getBoard();
        Color player = game.getCurrentPlayer();
        
        int row = player == Color.WHITE ? 0 : 7;
        int kingCol = 4;
        int toCol = kingside ? 6 : 2;
        
        if (board.isCellOccupied(row, kingCol))
        {
            Optional<Piece> piece = board.getPieceAt(row, kingCol);
            if (piece.isPresent() && piece.get().getClass().getSimpleName().equals("King"))
            {
                return game.movePiece(row, kingCol, row, toCol);
            }
        }
        
        return false;
    }
    
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
