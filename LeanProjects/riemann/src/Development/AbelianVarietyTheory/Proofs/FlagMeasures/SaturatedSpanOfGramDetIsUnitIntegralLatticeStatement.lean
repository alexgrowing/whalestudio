import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedSpanOfGramDetIsUnitIntegralLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturated_span_of_gramDet_isUnit_integralLattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule M.L.O V) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (m : ι → V) (hm : ∀ i, m i ∈ Λ) (hdet : IsUnitO M (H.gram m).det), ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range m) → v ∈ Submodule.span M.L.O (Set.range m) := by
  first | exact @GlobalTheory.satur_of_gram_det_unit | exact GlobalTheory.satur_of_gram_det_unit | (intros; apply GlobalTheory.satur_of_gram_det_unit <;> assumption)
