import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalization
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_ample_spread_from_localization : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (q : PrimeSpectrum R) (A : Over (Sp R)) (M : LB A.left), IsProper A.hom → M.IsLB → ∀ (B : Over (Sp (Localization.AtPrime q.asIdeal))) (φ : B.left ⟶ A.left) (N : LB B.left), IsPullback φ B.hom A.hom (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) → N.IsLB → LBIso N (M.pull φ) → Out.RelAmple B N → ∃ (U : (Sp R).Opens) (_ : q ∈ U), Out.RelAmple (Over.mk (A.hom ∣_ U)) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.AmpleSpreadAt.relAmple_spread_at | exact GlobalTheory.AmpleSpreadAt.relAmple_spread_at | (intros; apply GlobalTheory.AmpleSpreadAt.relAmple_spread_at <;> assumption)
