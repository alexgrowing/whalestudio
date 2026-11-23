import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tl_free_finrank : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K), Module.Free ℤ_[l] (Tl l A) ∧ Module.Finite ℤ_[l] (Tl l A) ∧ Module.finrank ℤ_[l] (Tl l A) = 2 * A.dim ∧ Module.Finite ℚ_[l] (Vl l A) ∧ Module.finrank ℚ_[l] (Vl l A) = 2 * A.dim := by
  intro K _ l _ hl A
  have hc : ∀ n : ℕ, Nat.card {x : A.Pt // x ^ (l ^ n) = 1} = l ^ (2 * A.dim * n) := by
    intro n
    have h := GlobalTheory.T.card_torsion_geometricPoints_eq_pow_two_dim K A (l ^ n) (by push_cast; exact pow_ne_zero _ hl)
    rw [h, ← pow_mul, mul_comm n]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.TateFree.free_finite_finrank A.Pt l (2 * A.dim) hc
  refine ⟨h1, h2, h3, inferInstance, ?_⟩
  rw [Module.finrank_baseChange, h3]

end GlobalTheory.AV.AbVar
