{-# OPTIONS --without-K --safe #-}
module Games.TicTacToe where

open import Level
open import Function using (_$_; _∘_; case_of_)

open import Data.Bool using (true; false)
open import Data.Product using (Σ-syntax; Σ; _,_)
open import Data.Unit using (⊤)

open import Data.Nat using (ℕ; zero; suc)

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
import Data.Fin.Properties as Finₚ

open import Data.List using (List; _∷_; [])
import Data.List as List

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybeₚ

open import Data.String using (String)
import Data.String as String

open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Nullary.Decidable as Dec

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import Reflection

--------------------------------------------------------------------------------
-- Players

data Player : Set where
  X : Player
  O : Player

other : Player → Player
other X = O
other O = X

player-dec : Decidable {A = Player} _≡_
player-dec X X = yes refl
player-dec X O = no λ ()
player-dec O X = no λ ()
player-dec O O = yes refl

∃-player? : ∀ {P : Player → Set} → Dec (P X) → Dec (P O) → Dec (Σ Player P)
∃-player? (yes PX) PO? = yes (X , PX)
∃-player? (no _) (yes PO) = yes (O , PO)
∃-player? (no ¬PX) (no ¬PO) = no λ { (X , PX) → ¬PX PX ; (O , PO) → ¬PO PO }

--------------------------------------------------------------------------------
-- Boards
--
-- We represent a tic-tac-toe board as something that can be indexed by two 'Fin 3' for convienences sake.
-- This is by no means the most efficient representation, but it makes a lot of the following
-- work a lot simpler, especially for victor condition.

Board : Set 
Board = Fin 3 → Fin 3 → Maybe Player

empty : Board
empty = λ _ _ → nothing

-- Decide if a player has placed a mark at a given position.
at? : ∀ (row col : Fin 3) → (p : Player) → (b : Board) → Dec (b row col ≡ just p)
at? row col p b  = Maybeₚ.≡-dec player-dec (b row col) (just p)

--------------------------------------------------------------------------------
-- Predicates for victory conditions
--
-- As noted before, the 'Fin 3' indexing encoding makes this a lot simpler.

Across : Player → Board → Set
Across m b = Σ[ row ∈ Fin 3 ] ∀ col → b row col ≡ just m

across? : ∀ p b → Dec (Across p b)
across? p b = Finₚ.any? λ row → Finₚ.all? λ col → Maybeₚ.≡-dec player-dec (b row col) (just p)

Down : Player → Board → Set
Down m b = Σ[ col ∈ Fin 3 ] ∀ row → b row col ≡ just m

down? : ∀ p b → Dec (Down p b)
down? p b = Finₚ.any? λ col → Finₚ.all? λ row → at? row col p b

Diag : Player → Board → Set
Diag m b = ∀ i → b i i ≡ just m

diag? : ∀ p b → Dec (Diag p b)
diag? p b = Finₚ.all? λ i → at? i i p b

data Win (p : Player) (b : Board) : Set where
  across : Across p b → Win p b
  down : Down p b → Win p b
  diag : Diag p b → Win p b

win? : ∀ p b → Dec (Win p b)
win? p b with across? p b | down? p b | diag? p b
... | yes pf | _ | _ = yes (across pf)
... | no _ | yes pf | _ = yes (down pf) 
... | no _ | no _ | yes pf = yes (diag pf)
... | no ¬across | no ¬down | no ¬diag = no λ { (across pf) → ¬across pf ; (down pf) → ¬down pf ; (diag pf) → ¬diag pf }

Full : Board → Set
Full b = ∀ row col → Σ[ p ∈ Player ] b row col ≡ just p

full? : ∀ b → Dec (Full b)
full? b = Finₚ.all? λ row → Finₚ.all? λ col → ∃-player? (at? row col X b) (at? row col O b)

record Tie (b : Board) : Set where
  constructor tied
  field
    full : Full b 
    not-win : ¬ (Σ[ p ∈ Player ] (Win p b))

tie? : ∀ b → Dec (Tie b)
tie? b with full? b | (∃-player? (win? X b) (win? O b)) 
... | yes full | no ¬win = yes (tied full ¬win)
... | no ¬full | _ = no λ { (tied full not-win) → ¬full full }
... | _ | yes win = no λ { (tied full not-win) → not-win win }

data GameOver (b : Board) : Set where
  win : (p : Player) → Win p b → GameOver b
  tie : Tie b → GameOver b

game-over? : ∀ b → Dec (GameOver b)
game-over? b with (∃-player? (win? X b) (win? O b)) | tie? b
... | yes (p , is-win) | _ = yes (win p is-win)
... | _ | yes is-tie = yes (tie is-tie)
... | no ¬win | no ¬tie = no λ { (win p w) → ¬win (p , w) ; (tie t) → ¬tie t }

--------------------------------------------------------------------------------
-- Reflection Tactics
--
-- We are going to be having to prove a lot of board validity conditions,
-- and constantly showing that the game is not over, so let's add a bit
-- of reflection to make use of our decidability proofs from before.

-- FIXME: For some reason, our custom type errors aren't being displayed.
-- I suspect this is because the error happens when unifying somewhere else,
-- but I don't feel like fixing it.

valid-tactic : Term → TC ⊤ 
valid-tactic hole = do
  soln ← quoteTC (refl {A = Maybe Player} {x = nothing})
  catchTC (unify hole soln) (typeError (strErr "That space is already occupied!" ∷ []))

-- [NOTE: Decision Procedures + Tactics]
-- We use Dec.from-yes + Dec.from-no here to ensure that no computation
-- occurs, and that we can recover the proposition via unification.
game-over-tactic : Board → Term → TC ⊤
game-over-tactic b hole = do
  soln ← quoteTC (Dec.from-yes (game-over? b))
  catchTC (unify hole soln) (typeError (strErr "The game is not over!" ∷ []))

game-not-over-tactic : Board → Term → TC ⊤
game-not-over-tactic b hole = do
  soln ← quoteTC (Dec.from-no (game-over? b))
  catchTC (unify hole soln) (typeError (strErr "The game is over!" ∷ []))

--------------------------------------------------------------------------------
-- Moves
--
-- A game is simply a series of alternating moves.
-- Note the use of the tactic arguments in 'Move'.

record Move (p : Player) (b : Board) : Set where
  constructor move
  field
    row : Fin 3
    col : Fin 3
    @(tactic valid-tactic) {valid} : b row col ≡ nothing
    @(tactic game-not-over-tactic b) {not-over} : ¬ (GameOver b)

-- Let a move act on a board.
play : ∀ {p b} → Move p b → Board
play {p = p} {b = b} (move row col) i j with row Finₚ.≟ i | col Finₚ.≟ j
... | yes _ | yes _ = just p
... | _ | _ = b i j

data Moves : Player → Board → Set where
  naught : ∀ {b} → (m : Move O b) → Moves X (play m) → Moves O b
  cross : ∀ {b} → (m : Move X b) → Moves O (play m) → Moves X b
  game-over : ∀ {p b} → {@(tactic game-over-tactic b) g : GameOver b} → Moves p b

Game : Set
Game = Moves X empty

--------------------------------------------------------------------------------
-- Goal Display Helpers
--
-- When you are playing a game, at any point you can simply add 'display-board'
-- to see the current board state.

print-player : Maybe Player → String
print-player (just X) = "X"
print-player (just O) = "O"
print-player nothing = " "

print-board : Board → String
print-board b = String.intersperse "---------\n" (List.map (λ col → (String.intersperse " | " (List.tabulate (print-player ∘ col))) String.++ "\n") (List.tabulate b))

display-board-macro : Term → TC ⊤
display-board-macro hole = do
  goal ← inferType hole
  case goal of λ {
      (def (Moves) (_ ∷ vArg board-tm ∷ [])) → do
        board ← unquoteTC board-tm
        typeError (strErr "Board:\n\n" ∷ strErr (print-board board) ∷ [])
      ;
      _ → typeError (strErr "Tried to display something that wasn't a board." ∷ [])
    }

macro
  display-board : Term → TC ⊤
  display-board = display-board-macro

--------------------------------------------------------------------------------
-- Examples

private
  -- Here's an example game. Try messing around with it!
  example : Game
  example =
    cross (move 1F 1F) $
    naught (move 0F 0F) $
    cross (move 0F 1F) $
    naught (move 1F 0F) $
    cross (move 2F 1F) $
    game-over

  -- Here's how to use the 'display-board' macro
  display-example : Game
  display-example =
    cross (move 1F 1F) $
    naught (move 0F 0F) $
    cross (move 0F 1F) $
    display-board
