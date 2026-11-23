import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingIdentityMatchedFamilyClosedTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericGenericTermsClosedUnderLocalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFramesStatement

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem setQ_locClosed {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (S : Prop → Prop)
    (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (w : Point D.host.E (D.R.rS + 1)) (hw : ZhatOM (ZhatL F F') = ptMat w) (hG : Gval F F' ≠ 0)
    (FP : ∀ p : PlF D, LocNG.FPair (locH (zOf Y) p) D.R.rS)
    (hB : GlobalTheory.Unfold.Based (zOf Y) FP (Tu D u) (Tu D u') F F') :
    GlobalTheory.Unfold.LocClosed F F' (zOf Y) FP (setQ Y u u' S) := by
  have hRel : ∀ p, (FP p).RelG (LocNG.theta ((zOf Y).M p)) := fun p =>
    (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w F F' hw hG p).2 (FP p) (hB p)
  obtain ⟨hng, hgen, -, -⟩ := GlobalTheory.T.nonGeneric_generic_terms_closed_under_localUnitary D X Y u u' F F' w hw hG (zOf Y) FP hB hRel
  intro t t' Λ Λ' hΛ hΛ' hloc ht
  have hGt : ∀ s : TauC Y u u', s.G ≠ 0 → (Y.tO u u').G s ≠ 0 := fun s hs => by
    show Formalism.L2.SG.TermOp.Gt s ≠ 0
    simp [Formalism.L2.SG.TermOp.Gt, hs]
  have h1 := hGt t (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t Λ hΛ).1
  have h2 := hGt t' (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t' Λ' hΛ').1
  have hiff : (Y.tO u u').gener t ↔ (Y.tO u u').gener t' := by
    constructor
    · intro hg
      exact (hgen t t' Λ Λ' hΛ hΛ' hloc ⟨h1, hg⟩).2
    · intro hg'
      by_contra hg
      exact (hng t t' Λ Λ' hΛ hΛ' hloc ⟨h1, hg⟩).2 hg'
  have he : (¬ (Y.tO u u').gener t) = (¬ (Y.tO u u').gener t') := propext (not_congr hiff)
  exact ⟨h2, he ▸ ht.2⟩

theorem familyRowWeightSumUnfoldingIdentity_proof : FamilyWeightSumUnfoldingIdentity := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, ?_⟩
  intro C' Cl _ _ D large₂ X Y u u' _ K S TS cls hF γ _ Fm hT
  obtain ⟨hTS, hCR, -⟩ := hF
  subst hTS
  exact GlobalTheory.T.unfolding_identity_matched_family_closed_terms D X Y u u' _ cls hCR
    (fun F F' w hw hG FP hB => setQ_locClosed Y u u' S F F' w hw hG FP hB) γ Fm hT

end GlobalTheory.SnFam
