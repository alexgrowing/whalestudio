import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorApproximation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le : ∀ (p : ℕ) [Fact p.Prime] (n m g : ℕ) (d : ℂ_[p]) (A Cc : Fin g → Fin m → ℂ_[p]) (G : Matrix (Fin m) (Fin m) ℂ_[p])
    (M : Fin m → Fin g → ℂ_[p]), d ≠ 0 → (∀ k j, ‖Cc k j‖ ≤ 1) → (∀ k j, ‖Cc k j - A k j‖ ≤ (p : ℝ)⁻¹ ^ n) →
    (∀ i k, ‖M i k‖ ≤ 1) → ‖G.det‖ = 1 → (∀ i j, d * G i j = ∑ k, M i k * A k j) →
    ∃ K : Fin m → Fin g, ‖d‖ ^ m ≤ ‖(Matrix.of fun k j => A (K k) j).det‖ ∧
      ‖(Matrix.of fun k j => A (K k) j).det‖ ≤ 1 ∧
      ‖(Matrix.of fun k j => Cc (K k) j).det - (Matrix.of fun k j => A (K k) j).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  first | exact @GlobalTheory.MinorBound.exists_minor_ge | exact GlobalTheory.MinorBound.exists_minor_ge | (intros; apply GlobalTheory.MinorBound.exists_minor_ge <;> assumption)
