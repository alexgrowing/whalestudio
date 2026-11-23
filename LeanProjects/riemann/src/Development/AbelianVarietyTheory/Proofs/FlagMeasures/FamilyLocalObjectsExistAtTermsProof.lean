import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalObjectFamilyClassesDetermineRowsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRowsStatement

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem existFam : ExistFam := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hctx K S TS cls hF γ hP => ?_⟩
  have hTie : ConcTie X Y := hctx.2.2
  obtain ⟨hTS, _, hrow⟩ := hF
  obtain ⟨t₀, ht₀, hv, rfl⟩ := hP
  have hG : ∀ t ∈ TS, t.G ≠ 0 := by
    intro t ht h0
    rw [hTS] at ht
    apply ht.1
    show Gt t = 0
    simp [Gt, h0]
  have hrel : t₀.relevant := (GlobalTheory.T.nonGeneric_family_classes_determine_rows D X Y u u' hTie).2.2 t₀ hv
  exact GlobalTheory.T.exists_localObjectFamily_classesDetermineRows D X Y u u' TS cls hG hrow t₀ ht₀ hrel

end GlobalTheory.SnFam
