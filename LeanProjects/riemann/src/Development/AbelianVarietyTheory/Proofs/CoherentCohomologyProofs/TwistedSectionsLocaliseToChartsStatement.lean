import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TwistedSectionsLocaliseToCharts
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.twistedSections_localise_to_charts : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (I : Finset (Fin (m + 1))), (∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : (⨅ i ∈ I, nonzeroLocus (s i)) ≤ ⊤) a = 0 → ∃ k : ℕ, xProd R I ^ k • GrSum.of (hx ⊤) t a = 0) ∧ ∀ (t : ℤ) (y : SecOnR f (tw M H t) (⨅ i ∈ I, nonzeroLocus (s i))), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤), GrSum.of (hx _) t' (SecOnR.restrict f _ le_top a) = xProd R I ^ k • GrSum.of (hx _) t y := by
  first | exact @GlobalTheory.AbLaw.twisted_sections_localise | exact GlobalTheory.AbLaw.twisted_sections_localise | (intros; apply GlobalTheory.AbLaw.twisted_sections_localise <;> assumption)
