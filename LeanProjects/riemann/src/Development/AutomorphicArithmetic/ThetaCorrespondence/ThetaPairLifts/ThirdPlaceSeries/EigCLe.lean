import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.EigGoodTypes
theorem eigC_le_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (hMt : MtParTie D.nd D.naut D.ntypes) (hbc : Formalism.MainNotions.SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D)
    (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) :
    ∃ σ' : D.ntypes.Par, eigC D.nd D.naut i x ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' ∧ D.ntypes.goodPar σ' := by
  obtain ⟨-, Sig, ⟨P0, hP0, hB0⟩, hg⟩ := hx
  let σ' : D.ntypes.Par := P.ty.par.eP.symm ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩
  have hloc : ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w := fun w => by
    have e : P.ty.par.eP σ' = ⟨Sig, sig_parC h0 h4 h5 hB0 hg⟩ := Equiv.apply_symm_apply _ _
    rw [P.ty.par.locPar_def, e]
  refine ⟨σ', ?_, ?_⟩
  · rw [hMt i σ']
    refine iSup₂_le fun Q hQ => le_iSup₂_of_le Q ⟨Sig, fun w => (hloc w).symm, ?_⟩ le_rfl
    have hQ' : D.naut.ptV i Q = some x := hQ
    obtain ⟨Pa, hPa⟩ := hbc i Q
    have hperm := ((h41 i).2.1 P0 Q (by rw [hP0]; simp) (hP0.trans hQ'.symm)).1 _ _ hB0 hPa
    exact GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hPa
  · intro k
    simp only [D.ntypes.labPar_def, hloc]
    exact hg k
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp),
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → MtParTie D.nd D.naut D.ntypes → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.tie0 D →
    Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → GlobalTheory.NRows.GoodIdempotentFixesLocalisationForms D → GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector X → ∀ i, GlobalTheory.NJoin.EigGood X i := by
  intro hL D P X h41 _ hMt hbc h0 h4 h5 hE0 hRead i hμ j hj x hx f hf y hy
  obtain ⟨σ', hle, hgood⟩ := _root_.GlobalTheory.EigGoodTypes.eigC_le_alt P h41 hMt hbc h0 h4 h5 i x hx
  exact (hRead _ hμ j f y hy).1 (onMt_cast hj f (hE0 i σ' _ (hle hf) hgood))
end GlobalTheory.EigGoodTypes
end
end
