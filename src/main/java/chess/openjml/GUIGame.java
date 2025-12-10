package chess.openjml;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.net.URL;
import java.util.*;
import java.util.List;
import javax.imageio.ImageIO;
import javax.swing.*;

import chess.openjml.game.Game;
import chess.openjml.game.MoveResult;
import chess.openjml.moves.MovePair;
import chess.openjml.moves.Position;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;

public class GUIGame extends JFrame
{
    private static final int BOARD_SIZE = 8;
    private static final int STATUS_BAR_HEIGHT = 50;
    
    private final Game game;
    private final ChessBoardPanel boardPanel;
    private final JLabel statusLabel;
    private boolean gameOver;

    public GUIGame(Game game)
    {
        this.game = game;
        this.boardPanel = new ChessBoardPanel();
        this.statusLabel = createStatusLabel();
        this.gameOver = false;
        
        initializeFrame();
    }

    private void initializeFrame()
    {
        setTitle("Chess OpenJML");
        setDefaultCloseOperation(EXIT_ON_CLOSE);
        setResizable(false);
        
        add(boardPanel, BorderLayout.CENTER);
        add(statusLabel, BorderLayout.SOUTH);
        
        pack();
        setLocationRelativeTo(null);
        setVisible(true);
    }

    private JLabel createStatusLabel()
    {
        JLabel label = new JLabel();
        label.setHorizontalAlignment(SwingConstants.CENTER);
        label.setVerticalAlignment(SwingConstants.CENTER);
        label.setFont(new Font("Arial", Font.BOLD, 16));
        label.setPreferredSize(new Dimension(
            ChessBoardPanel.SQUARE_SIZE * BOARD_SIZE, 
            STATUS_BAR_HEIGHT
        ));
        updateStatusText(label);
        return label;
    }

    private void updateStatusText(JLabel label)
    {
        Color currentTurn = game.getCurrentTurn();
        String status = currentTurn + " to move";

        if (game.getBoard().someoneIsInCheck())
        {
            status += " (check)";
        }
        label.setText(status);
    }

    @Override
    public Dimension getPreferredSize()
    {
        int size = ChessBoardPanel.SQUARE_SIZE * BOARD_SIZE;
        return new Dimension(size, size + STATUS_BAR_HEIGHT);
    }

    private class ChessBoardPanel extends JPanel
    {
        private static final int SQUARE_SIZE = 60;
        private static final int IMAGE_PADDING = 10;
        private static final java.awt.Color LIGHT_SQUARE = new java.awt.Color(240, 217, 181);
        private static final java.awt.Color DARK_SQUARE = new java.awt.Color(181, 136, 99);
        private static final java.awt.Color SELECTED_COLOR = new java.awt.Color(255, 255, 0, 100);
        private static final java.awt.Color INVALID_COLOR = new java.awt.Color(250, 50, 50, 200);
        private static final java.awt.Color VALID_MOVE_COLOR = new java.awt.Color(60, 130, 60, 200);

        private final Map<String, BufferedImage> pieceImages;
        private final Set<Position> validMoves;
        private Position selectedPosition;
        private Position invalidPosition;

        public ChessBoardPanel()
        {
            this.pieceImages = new HashMap<>();
            this.validMoves = new HashSet<>();
            loadPieceImages();
            addMouseListener(new BoardClickListener());
        }

        private void loadPieceImages()
        {
            for (String color : Arrays.asList("white", "black"))
            {
                for (String piece : Arrays.asList("pawn", "bishop", "knight", "rook", "queen", "king"))
                {
                    loadPieceImage(color, piece);
                }
            }
        }

        private void loadPieceImage(String color, String piece)
        {
            String key = color + "_" + piece;
            String path = "/graphics/" + key + ".png";

            try
            {
                URL resource = getClass().getResource(path);
                if (resource == null)
                {
                    System.err.println("Resource not found: " + path);
                    return;
                }
                BufferedImage original = ImageIO.read(resource);
                BufferedImage scaled = scaleImage(original, SQUARE_SIZE - IMAGE_PADDING);
                pieceImages.put(key, scaled);
            }
            catch (IOException ex)
            {
                System.err.println("Failed to load: " + path);
            }
        }

        private BufferedImage scaleImage(BufferedImage original, int size)
        {
            BufferedImage scaled = new BufferedImage(size, size, BufferedImage.TYPE_INT_ARGB);
            Graphics2D g2d = scaled.createGraphics();
            g2d.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_BILINEAR);
            g2d.drawImage(original, 0, 0, size, size, null);
            g2d.dispose();
            return scaled;
        }

        @Override
        protected void paintComponent(Graphics g)
        {
            super.paintComponent(g);
            Graphics2D g2d = (Graphics2D) g;

            for (int row = 0; row < BOARD_SIZE; row++)
            {
                for (int col = 0; col < BOARD_SIZE; col++)
                {
                    drawSquare(g2d, row, col);
                    drawPieceIfPresent(g2d, row, col);
                }
            }
        }

        private void drawSquare(Graphics2D g2d, int row, int col)
        {
            int x = col * SQUARE_SIZE;
            int y = (BOARD_SIZE - 1 - row) * SQUARE_SIZE;

            g2d.setColor(isLightSquare(row, col) ? LIGHT_SQUARE : DARK_SQUARE);
            g2d.fillRect(x, y, SQUARE_SIZE, SQUARE_SIZE);

            g2d.setColor(java.awt.Color.BLACK);
            g2d.setStroke(new BasicStroke(1));
            g2d.drawRect(x, y, SQUARE_SIZE, SQUARE_SIZE);

            drawHighlight(g2d, row, col, x, y);
        }

        private boolean isLightSquare(int row, int col)
        {
            return (row + col) % 2 == 0;
        }

        private void drawHighlight(Graphics2D g2d, int row, int col, int x, int y)
        {
            Position pos = new Position(row, col);
            
            if (pos.equals(selectedPosition))
            {
                g2d.setColor(SELECTED_COLOR);
                g2d.fillRect(x, y, SQUARE_SIZE, SQUARE_SIZE);
            }
            else if (pos.equals(invalidPosition))
            {
                g2d.setColor(INVALID_COLOR);
                g2d.fillRect(x, y, SQUARE_SIZE, SQUARE_SIZE);
            }
            else if (validMoves.contains(pos))
            {
                drawValidMoveIndicator(g2d, x, y);
            }
        }

        private void drawValidMoveIndicator(Graphics2D g2d, int x, int y)
        {
            int dotRadius = 8;
            int centerX = x + SQUARE_SIZE / 2;
            int centerY = y + SQUARE_SIZE / 2;
            g2d.setColor(VALID_MOVE_COLOR);
            g2d.fillOval(centerX - dotRadius, centerY - dotRadius, dotRadius * 2, dotRadius * 2);
        }

        private void drawPieceIfPresent(Graphics2D g2d, int row, int col)
        {
            game.getBoard().getPieceAt(new Position(row, col)).ifPresent(piece ->
            {
                int x = col * SQUARE_SIZE;
                int y = (BOARD_SIZE - 1 - row) * SQUARE_SIZE;
                drawPiece(g2d, piece, x, y);
            });
        }

        private void drawPiece(Graphics2D g2d, Piece piece, int x, int y)
        {
            BufferedImage image = pieceImages.get(getPieceImageKey(piece));
            if (image != null)
            {
                int imageX = x + (SQUARE_SIZE - image.getWidth()) / 2;
                int imageY = y + (SQUARE_SIZE - image.getHeight()) / 2;
                g2d.drawImage(image, imageX, imageY, null);
            }
        }

        private String getPieceImageKey(Piece piece)
        {
            return piece.getColor().toString().toLowerCase() + "_" + piece.getClass().getSimpleName().toLowerCase();
        }

        private Position screenToBoard(int mouseX, int mouseY)
        {
            int col = mouseX / SQUARE_SIZE;
            int row = (BOARD_SIZE - 1) - (mouseY / SQUARE_SIZE);
            return new Position(row, col);
        }

        private void clearSelection()
        {
            selectedPosition = null;
            validMoves.clear();
            invalidPosition = null;
        }

        private class BoardClickListener extends MouseAdapter
        {
            @Override
            public void mouseClicked(MouseEvent e)
            {
                if (gameOver)
                {
                    return;
                }

                Position clickedPos = screenToBoard(e.getX(), e.getY());

                if (!game.getBoard().isWithinBounds(clickedPos))
                {
                    return;
                }

                if (selectedPosition == null)
                {
                    handlePieceSelection(clickedPos);
                }
                else
                {
                    handleMoveAttempt(clickedPos);
                }
            }

            private void handlePieceSelection(Position pos)
            {
                game.getBoard().getPieceAt(pos)
                    .filter(piece -> piece.isAlly(game.getCurrentTurn()))
                    .ifPresent(piece ->
                    {
                        selectedPosition = pos;
                        validMoves.clear();
                        validMoves.addAll(piece.getValidMoves(game.getBoard()));
                        invalidPosition = null;
                        repaint();
                    });
            }

            private void handleMoveAttempt(Position targetPos)
            {
                if (selectedPosition.equals(targetPos))
                {
                    clearSelection();
                    repaint();
                    return;
                }

                MovePair move = new MovePair(selectedPosition, targetPos);
                MoveResult result = game.move(move);

                if (result == MoveResult.INVALID)
                {
                    invalidPosition = targetPos;
                    repaint();
                    return;
                }

                clearSelection();
                updateStatusText(statusLabel);

                if (result == MoveResult.CHECKMATE)
                {
                    statusLabel.setText("Checkmate! " + game.getCurrentTurn().opposite() + " wins!");
                    gameOver = true;
                }
                else if (result == MoveResult.DRAW)
                {
                    statusLabel.setText("The game is a draw!");
                    gameOver = true;
                }
                
                repaint();
            }
        }
    }
}