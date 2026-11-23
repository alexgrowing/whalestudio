import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlagB

noncomputable section

open Matrix Module
open scoped ContDiff

namespace PositivityTheory.RgBcC.VC.GFC

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC.GFB
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Blocks

variable (blk : Fin n → ℕ)

def IsUp (N : Mat n) : Prop := ∀ a b, ¬ blk a < blk b → N a b = 0

def IsDiag (y : Mat n) : Prop := ∀ a b, blk a ≠ blk b → y a b = 0

def S0 (c : Fin n → ℂ) : Prop := ∀ j, blk j ≠ 0 → c j = 0

def S1 (c : Fin n → ℂ) : Prop := ∀ j, blk j = 2 → c j = 0

variable {blk}

end Blocks

end PositivityTheory.RgBcC.VC.GFC
