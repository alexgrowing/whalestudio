import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePointDualBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_point_dual_basis : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C) {n : ℕ} (r : Fin n → O) (a : Fin n → 𝓞 E), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then d else 0) → ∀ {w : P.V}, w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ → d • w ∈ P.latT := by
  first | exact @GlobalTheory.HTLat.Point.smul_latTQuot_le_latT | exact GlobalTheory.HTLat.Point.smul_latTQuot_le_latT | (intros; apply GlobalTheory.HTLat.Point.smul_latTQuot_le_latT <;> assumption)
