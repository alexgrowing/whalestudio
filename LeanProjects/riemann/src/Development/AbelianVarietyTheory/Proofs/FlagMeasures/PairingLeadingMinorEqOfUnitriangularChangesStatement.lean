import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingLeadingMinorEqOfUnitriangularChanges
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' g g' : Fin (r + 1) → V) (hg : Tri E f g) (hg' : Tri E f' g') (l : ℕ), H.Dl g g' l = H.Dl f f' l := by
  first | exact @GlobalTheory.MinorTri.Dl_eq_of_tri | exact GlobalTheory.MinorTri.Dl_eq_of_tri | (intros; apply GlobalTheory.MinorTri.Dl_eq_of_tri <;> assumption)
