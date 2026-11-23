import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocusCodimBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_locus_codim_bound : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → ∃ (U : B.X.Opens) (n : ℕ), 0 < n ∧ f.fibreDeg 1 = n ∧ topologicalKrullDim ((U : Set B.X)ᶜ : Set B.X) + 1 ≤ (B.relDim : WithBot ℕ∞) ∧ ∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧ (letI := (f.f.app V).hom.toAlgebra; Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n) := by
  first | exact @GlobalTheory.Vert.Model.Hom.exists_finite_free_off_codim_two | exact GlobalTheory.Vert.Model.Hom.exists_finite_free_off_codim_two | (intros; apply GlobalTheory.Vert.Model.Hom.exists_finite_free_off_codim_two <;> assumption)
