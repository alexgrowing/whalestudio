import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem toReal_mem_psdCone_of_pos_int : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) →
    (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (id : ℤ → ℤ) (Fin r → ℤ) := by
  intro r b hs hp
  refine TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hs) fun y => ?_
  by_cases hy : y = 0
  · subst hy; simp
  · exact (hp y hy).le

end GlobalTheory.Poinc
