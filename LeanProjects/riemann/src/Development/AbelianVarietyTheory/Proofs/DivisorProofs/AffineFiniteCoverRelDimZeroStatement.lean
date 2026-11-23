import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteCoverRelDimZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_finite_cover_rel_dim_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), f.relDim = 0 → ∀ y : B.X, ringKrullDim (B.X.presheaf.stalk y) ≤ 1 → ∃ V : B.X.Opens, y ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧ (letI := (f.f.app V).hom.toAlgebra; Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Vert.FiniteNear.exists_affine_finite | exact GlobalTheory.Vert.FiniteNear.exists_affine_finite | (intros; apply GlobalTheory.Vert.FiniteNear.exists_affine_finite <;> assumption)
