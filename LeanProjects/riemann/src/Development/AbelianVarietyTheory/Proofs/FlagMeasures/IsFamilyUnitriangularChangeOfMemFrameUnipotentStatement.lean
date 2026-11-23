import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFamilyUnitriangularChangeOfMemFrameUnipotent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (Fr : FrameD H r), ∀ n ∈ Fr.N, Tri E Fr.f (fun b => n (Fr.f b)) := by
  first | exact @GlobalTheory.NFrameTri.tri_of_mem_N | exact GlobalTheory.NFrameTri.tri_of_mem_N | (intros; apply GlobalTheory.NFrameTri.tri_of_mem_N <;> assumption)
