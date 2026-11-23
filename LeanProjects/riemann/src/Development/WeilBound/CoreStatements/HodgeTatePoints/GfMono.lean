import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_mono : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ϖ ϖ' : o) (N : ℕ) (b : Fin N → K → ℤ), ϖ' ∣ ϖ → Num.TrivFlagMod o ϖ y N b → Num.TrivFlagMod o ϖ' y N b := by
  intro o _ Ω _ _ K _ J _ y ϖ ϖ' N b ⟨c, hc⟩ ⟨g, h1, h2⟩
  refine ⟨g, fun s hs => ?_, fun s t hs ht => ?_⟩
  · obtain ⟨hg, h, hh, r, hr, e⟩ := h1 s hs
    refine ⟨hg, h, hh, algebraMap o Ω c * r, mul_mem (Subalgebra.algebraMap_mem _ c) hr, ?_⟩
    rw [e, hc, map_mul, mul_assoc]
  · obtain ⟨m, U, Z, hU, hZ, hU0, hUd, hm, e⟩ := h2 s t hs ht
    refine ⟨m, U, algebraMap o Ω c • Z, hU, fun i j => ?_, hU0, hUd, hm, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_mem (Subalgebra.algebraMap_mem _ c) (hZ i j)
    · rw [e, hc, map_mul, mul_smul]

end PositivityTheory.HtPt.Gf
