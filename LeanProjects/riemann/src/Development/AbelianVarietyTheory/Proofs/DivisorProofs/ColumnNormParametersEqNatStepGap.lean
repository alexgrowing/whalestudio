import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace GlobalTheory.ColumnNormCompare

theorem numRec_eq_ofRecord : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) →
    GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  intro D L Del h0 hD hE
  have hm : (D.R.m : ℝ) ≠ 0 := by
    have := D.R.two_le_m
    exact_mod_cast (show D.R.m ≠ 0 by omega)
  have h1 : ⌊D.s.Del⌋₊ = Del := by rw [hD]; exact Nat.floor_natCast Del
  have h2 : ⌈LevelStarExponents.h0 L⌉₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [hE]; field_simp
    rw [this]; exact Nat.ceil_natCast h0
  simp only [numDatumOfParameters, ofRecord, h1, h2]

end GlobalTheory.ColumnNormCompare
