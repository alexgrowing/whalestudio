import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeRankGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_rank_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (V : B.X.Opens), (V : Set B.X).Nonempty → IsAffineOpen V → IsAffineOpen (f.f ⁻¹ᵁ V) → (letI := (f.f.app V).hom.toAlgebra; Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) → Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) → Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = Module.finrank f.fnField Γ(f.genFibre, ⊤)) := by
  first | exact @GlobalTheory.Vert.Model.Hom.finrank_sections_eq_finrank_genFibre | exact GlobalTheory.Vert.Model.Hom.finrank_sections_eq_finrank_genFibre | (intros; apply GlobalTheory.Vert.Model.Hom.finrank_sections_eq_finrank_genFibre <;> assumption)
