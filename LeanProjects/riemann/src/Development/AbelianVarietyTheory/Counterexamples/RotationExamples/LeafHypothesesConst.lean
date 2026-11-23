import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.L2.Indef Formalism.L2.Indef.Tree

noncomputable section

namespace GlobalTheory.LeafRestExamples

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

def constRecord (Df : DefSide Bs) (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (M : Submodule (𝓞 K) (Fin n → K)) (t : ℕ) : FunData K Df where
  n := n
  X' := X
  M := M
  vmu := fun _ => 0
  Tf := ∅
  dF := fun _ => 0
  m := 2
  rq := fun _ _ => 1
  dl := fun _ => 0
  Sd := ∅
  Se := ∅
  N0 := fun _ _ _ => 0
  zA := fun _ => 1
  zA' := fun _ => 1
  zT := fun _ _ => 1
  zTd := fun _ _ _ => 1
  gT := fun _ _ _ => 0
  ch := fun _ => true
  dd := fun _ => 0
  hd := fun _ => 0
  yy := fun _ => 0
  Sq := Unit
  S0 := ∅
  sv0 := ()
  cc := fun _ => 0
  qq := fun _ => 0
  f := 16
  k := 16
  tt := t
  cl := fun _ _ => 0
  g1 := 0
  g2 := 0
  pd := 0
  pd' := 0
  dE := 0
  Bw := 1

def truncZero (y : ℝ) : ℤ := if 0 ≤ y then ⌊y⌋ else ⌈y⌉

theorem abs_truncZero_le (y : ℝ) (a : ℤ) :
    |(truncZero y : ℝ)| ≤ |y| ∧ |((a + truncZero y : ℤ) : ℝ)| ≤ |(a : ℝ) + y| + |y| := by
  have key : |(truncZero y : ℝ)| ≤ |y| ∧ |(truncZero y : ℝ) - y| ≤ |y| := by
    unfold truncZero
    split_ifs with h
    · have h1 := Int.floor_le y
      have h2 : (0 : ℝ) ≤ (⌊y⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.mpr h
      rw [abs_of_nonneg h, abs_of_nonneg h2, abs_of_nonpos (by linarith)]
      constructor <;> linarith
    · push Not at h
      have h1 := Int.le_ceil y
      have h2 : ((⌈y⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_nonpos.mpr h.le
      rw [abs_of_neg h, abs_of_nonpos h2, abs_of_nonneg (by linarith)]
      constructor <;> linarith
  refine ⟨key.1, ?_⟩
  push_cast
  calc |(a : ℝ) + truncZero y| = |((a : ℝ) + y) + (truncZero y - y)| := by ring_nf
    _ ≤ |(a : ℝ) + y| + |(truncZero y : ℝ) - y| := abs_add_le _ _
    _ ≤ _ := by linarith [key.2]

end GlobalTheory.LeafRestExamples
