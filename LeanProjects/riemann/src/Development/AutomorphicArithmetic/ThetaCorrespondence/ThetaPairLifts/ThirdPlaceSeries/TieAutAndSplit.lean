import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIffStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecUnit
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.AutomorphismSplitting
theorem tieAut_and_split_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut ∧ ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v) := by
  intro hAF hL D P
  have hcsd : IsCSD D.host P.cf.eta := GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ P.cf.isEta
  have hE : (P.chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [P.chr.etaT]; exact P.cf.isEta.inf⟩
  have hE' : (P.chr.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => (-(1 / 2) : ℚ)) :=
    ⟨fun _ => -1, fun _ => by norm_num, by rw [P.chr.etaTinv]; exact hasInf_inv P.cf.isEta.inf⟩
  refine ⟨⟨⟨?_, ?_⟩, fun τ => ?_, fun w => ?_, fun i w => ?_⟩, fun k v => GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v⟩
  · rw [P.chr.csd, P.chr.etaT]; exact hcsd
  · rw [P.chr.csd, P.chr.etaTinv]; exact isCSD_inv' hcsd
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
    · have ht : τ = embPsi D.host (D.eTau ρ) := h.symm
      rw [ht, (P.chr.infG _ _ hE (D.eTau ρ)).1, (P.chr.infG _ _ hE' (D.eTau ρ)).1]
      refine ⟨Or.inl (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; rfl
    · have ht : τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) := by
        rw [← h]; ext x; rfl
      rw [ht, (P.chr.infG _ _ hE (D.eTau ρ)).2, (P.chr.infG _ _ hE' (D.eTau ρ)).2]
      refine ⟨Or.inr (by push_cast; rfl), ?_⟩
      rw [Multiset.map_singleton]; push_cast; ring_nf
  · have hu : D.naut.unr (D.naut.locG D.naut.etaT w) := D.naut.etaT_unr w
    rw [D.naut.tempered_unr _ hu, P.chr.frob _ w ((P.chr.unr_iff _ w).1 hu)]
    intro α hα
    rw [Multiset.mem_singleton] at hα
    subst hα
    have h1 : ‖(((P.chr.e1 D.naut.etaT).1.val w : ℂˣ) : ℂ)‖ = 1 :=
      (P.chr.e1 D.naut.etaT).2 _
    rw [Units.val_inv_eq_inv_val, norm_inv, h1, inv_one]
  · obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E (P.chr.e1 (D.naut.muC i)).1 w
    have he := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P (D.naut.muC i) w ξ hξ
    rw [P.T.tempered, he]
    refine GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig _ _ _ _ _ _ ?_ ?_
    · rw [← he, P.T.dim, D.naut.locG_dim]
    · intro φ _ α hα
      exact _root_.UpperTheory.Zero.LLC.IsRecT.recUnit (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) ξ
        (Irr.ofDet 1 ξ hξ.1) (hξu (P.chr.e1 _).2) ⟨Representation.Equiv.refl _⟩ φ α hα
end GlobalTheory.AutomorphismSplitting
end
