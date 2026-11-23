import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatCoverExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_cover_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (U : B.X.Opens) (n : ℕ), (∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧ (letI := (f.f.app V).hom.toAlgebra; Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n)) → ∀ (G : B.X.Modules) [IsFiniteQC G], B.IsVertical G → suppDim G ≤ 0 → support G ⊆ (U : Set B.X) → chiLen O ((Scheme.Modules.pullback f.f).obj G) = n * chiLen O G := by
  first | exact @GlobalTheory.ProjBase.chiLen_pullback_eq_mul | exact GlobalTheory.ProjBase.chiLen_pullback_eq_mul | (intros; apply GlobalTheory.ProjBase.chiLen_pullback_eq_mul <;> assumption)
