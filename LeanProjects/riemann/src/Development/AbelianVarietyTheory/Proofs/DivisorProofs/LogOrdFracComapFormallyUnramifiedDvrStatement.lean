import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogOrdFracComapFormallyUnramifiedDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)], (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) → ∀ g : K, g ≠ 0 → WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  first | exact @GlobalTheory.RestrictOrd.log_ordFrac_comap | exact GlobalTheory.RestrictOrd.log_ordFrac_comap | (intros; apply GlobalTheory.RestrictOrd.log_ordFrac_comap <;> assumption)
