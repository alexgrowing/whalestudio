import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds

section Perm

variable {d : ℕ} (c : Composition d)

def bsig (i : Fin d) : Fin d :=
  ⟨c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i, by
    have a1 := c.sizeUpTo_index_le i
    have a2 := c.lt_sizeUpTo_index_succ i
    simp only [Fin.val_succ] at a2
    have a3 : c.sizeUpTo ((c.index i : ℕ) + 1) ≤ d := c.sizeUpTo_le _
    omega⟩

theorem bsig_val (i : Fin d) :
    ((bsig c i : Fin d) : ℕ) = c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i := rfl

theorem bsig_index (i : Fin d) : c.index (bsig c i) = c.index i := by
  have a1 := c.sizeUpTo_index_le i
  have a2 := c.lt_sizeUpTo_index_succ i
  simp only [Fin.val_succ] at a2
  apply index_unique c (bsig c i) (c.index i)
  · rw [bsig_val]; omega
  · rw [bsig_val]; omega

theorem bsig_bsig (i : Fin d) : bsig c (bsig c i) = i := by
  have a1 := c.sizeUpTo_index_le i
  have a2 := c.lt_sizeUpTo_index_succ i
  simp only [Fin.val_succ] at a2
  apply Fin.ext
  rw [bsig_val, bsig_index, bsig_val]
  omega

def bperm : Equiv.Perm (Fin d) := Function.Involutive.toPerm (bsig c) (bsig_bsig c)

end Perm

section Minor

variable {E : Type} [Field E] {d : ℕ}

end Minor

theorem max_mul_le {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) : max 1 (x * z) ≤ max 1 x * max 1 z := by
  have h1 : (1 : ℝ) ≤ max 1 x := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 z := le_max_left _ _
  apply max_le
  · nlinarith
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hz (by linarith)

def pre (y : ℕ → ℝ) (a : ℕ) : ℝ := ∏ i ∈ range (a + 1), y i

section Ends

variable {E : Type} [Field E] {d : ℕ}

def bEnd (p : Point E d) (a : Fin (toComp p).length) : E :=
  leadMinorE (ptMat p) ((toComp p).sizeUpTo ((a : ℕ) + 1))

def yN (τ : E →+* ℂ) (p : Point E d) (i : ℕ) : ℝ :=
  if h : i < (toComp p).length then ‖τ (toT p ⟨i, h⟩)‖ ^ (toComp p).blocksFun ⟨i, h⟩ else 1

end Ends

end Formalism.MainNotions.S.Pv.HH

end
