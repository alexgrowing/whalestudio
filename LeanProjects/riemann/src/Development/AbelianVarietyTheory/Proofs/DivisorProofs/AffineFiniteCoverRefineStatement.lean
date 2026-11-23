import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteCoverRefine
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_finite_cover_refine : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B.X → ∀ y : B.X, ringKrullDim (B.X.presheaf.stalk y) ≤ 1 → ∀ V : B.X.Opens, y ∈ V → IsAffineOpen V → IsAffineOpen (f.f ⁻¹ᵁ V) → (letI := (f.f.app V).hom.toAlgebra; Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V)) → ∃ V' : B.X.Opens, y ∈ V' ∧ IsAffineOpen V' ∧ IsAffineOpen (f.f ⁻¹ᵁ V') ∧ (letI := (f.f.app V').hom.toAlgebra; Module.Free Γ(B.X, V') Γ(B'.X, f.f ⁻¹ᵁ V') ∧ Module.Finite Γ(B.X, V') Γ(B'.X, f.f ⁻¹ᵁ V')) := by
  first | exact @GlobalTheory.GoodOpenFree.exists_free_nbhd | exact GlobalTheory.GoodOpenFree.exists_free_nbhd | (intros; apply GlobalTheory.GoodOpenFree.exists_free_nbhd <;> assumption)
