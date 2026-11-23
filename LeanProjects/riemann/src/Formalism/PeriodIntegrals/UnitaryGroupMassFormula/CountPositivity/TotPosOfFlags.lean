import Mathlib
import Formalism.PeriodIntegrals.CntLocalParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.LeadingMinorFullEqProd

noncomputable section

namespace PI.CntNotPosW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem totPos_of_flags (D : Formalism.BasicNotions.D7) {T T' : ℕ} (F : FlagG (VS D) D.R.rS (T : D.host.E))
    (F' : FlagG (VS D) D.R.rS (T' : D.host.E)) (hG : Gflag F F' ≠ 0) : TotPos (Gflag F F') := by
  unfold TotPos
  intro τ
  haveI := D.host.isCMField_hostE
  refine gflag_pos (p' := ((VS D).sig (embS D τ)).1) (q' := ((VS D).sig (embS D τ)).2) F F' (embS D τ)
    (fun a => NumberField.IsCMField.complexEmbedding_complexConj _ (embS D τ) a) (D.sp.Y_sig 0 (embS D τ)) ?_ hG
  rw [D.sp.baseSpace_signature_eq]
  rfl

theorem notPosAll : PI.CntLocalParts.NotPosAll := by
  intro D δ M hA L u u' hT F0 what₂ hR Z hZ
  have hE : ∀ Λ, EZ (Tn u') F0 Λ Z = ∅ := by
    intro Λ
    ext F'
    simp only [EZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, _, hG⟩, _, _, _, hZ'⟩
    apply hZ
    have h1 : GZ (Tn u) (Tn u') Z = Gflag F0 F'.fl := by rw [← hZ']; rfl
    rw [h1]
    exact totPos_of_flags D F0 F'.fl hG
  have hc : ∀ Λ, cntE (Tn u') F0 Λ Z = 0 := by
    intro Λ
    simp only [cntE, hE Λ, Set.mem_empty_iff_false, false_and, exists_false, Set.ofPred_false,
      Set.encard_empty]
  simp [Formalism.L2.SG.CntLocal.nu, hc]

end PI.CntNotPosW
