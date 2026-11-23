import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQpStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SerChar
open GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.SplitRead
theorem locG_muC_eq_rcw_alt_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (k : Fin 2) (w : PlE D.host) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w), (∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n), Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) → P.T.e w (rcw n π) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) → D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 (((P.tp.tup (D.nd.mu i) j).loc w).comp (Units.map e.toMonoidHom)))) := by
  intro hPr hL D P i j hj k w e rcw hrcw
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have hc : GlobalTheory.NPin.IsComp (P.chr.e1 (D.naut.muC i)).1 w ((P.tp.tup (D.nd.mu i) j).loc w) := by
    rw [P.chr.muC i j hj]
    exact ⟨ParLaws.isSmoothChar_loc _ w, fun _ => rfl⟩
  have h1 := _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp hPr.fin hL D P (D.naut.muC i) w _ hc
  have φ : Representation.Equiv
      (Model.detRep 1 (((P.tp.tup (D.nd.mu i) j).loc w).comp (Units.map e.toMonoidHom)))
      ((Irr.ofDet 1 ((P.tp.tup (D.nd.mu i) j).loc w) hc.1).toIrrRep.ρ.comp
        (Matrix.GeneralLinearGroup.map e.toRingHom)) := by
    refine Representation.Equiv.mk (LinearEquiv.refl ℂ ℂ) fun g => ?_
    ext
    change (Model.detRep 1 (((P.tp.tup (D.nd.mu i) j).loc w).comp (Units.map e.toMonoidHom)) g) 1 =
      (GlobalTheory.SmGL.detRep (Fin 1) ((P.tp.tup (D.nd.mu i) j).loc w) (Matrix.GeneralLinearGroup.map e.toRingHom g)) 1
    rw [GlobalTheory.SmGL.detRep, ofChar_apply, detChar_apply, det_map_units]
    simp [Model.detRep, Model.chRep]
  have h2 := hrcw 1 (Irr.ofDet 1 ((P.tp.tup (D.nd.mu i) j).loc w) hc.1).toIrrRep
    (Rep.of (Model.detRep 1 (((P.tp.tup (D.nd.mu i) j).loc w).comp (Units.map e.toMonoidHom)))) ⟨Rep.mkIso φ⟩
  apply (P.T.e w).injective
  rw [h1, h2]
  rfl
end GlobalTheory.SerChar
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_split_qp_alt_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (k : Fin 2) (w : PlE D.host) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w), (∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n), Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) → P.T.e w (rcw n π) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) → D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 (((P.tp.tup (D.nd.mu i) j).loc w).comp (Units.map e.toMonoidHom)))) := by
  first | exact @_root_.GlobalTheory.SerChar.locG_muC_eq_rcw_alt_alt | exact _root_.GlobalTheory.SerChar.locG_muC_eq_rcw_alt_alt | (intros; apply _root_.GlobalTheory.SerChar.locG_muC_eq_rcw_alt_alt <;> assumption)
end
end
