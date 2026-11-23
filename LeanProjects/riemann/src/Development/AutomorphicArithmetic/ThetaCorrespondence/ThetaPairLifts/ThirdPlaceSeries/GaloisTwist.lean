import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightTwistCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwistGal
theorem galois_twist_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
  intro hB hL D P i a ρ χ hρ hχ
  have htc : Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) :=
    GlobalTheory.TwistGal.cont_twGL ρ χ hρ hχ
  have hdR : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ} (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))),
      Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))) →
      (D.naut.IsdRW i r w ↔ GlobalTheory.Pst.IsdRAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
    intro w hw b r hr
    rw [(P.wdOf i b r w).2.2.2.1]
    exact GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw (D.nd.O i) (D.nbr i w hw) (D.nbr_ind i w hw) b r hr
  have p1 : ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w) := by
    intro w hw h
    rw [hdR w hw χ hχ] at h
    rw [hdR w hw _ htc, hdR w hw ρ hρ]
    rw [GlobalTheory.Pst.resDec, GlobalTheory.TwistGal.comp_twGL]
    exact GlobalTheory.T.deRham_characterTwist_iff_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om _ (D.nd.O i) (D.nbr i w hw) a (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) (GlobalTheory.Pst.resDec D.nd.plOm.1 χ w) (hρ.comp continuous_subtype_val) (hχ.comp continuous_subtype_val) h
  have p3 : ∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c) := by
    intro τ c h hc
    have w0 : HeightOneSpectrum (𝓞 D.host.E) := PI.CompDegEF.plOf τ
    rw [(P.wdOf i 1 χ w0).2.2.2.2 τ] at hc
    rw [(P.wdOf i a _ w0).2.2.2.2 τ, (P.wdOf i a ρ w0).2.2.2.2 τ]
    refine GlobalTheory.T.hodgeTateJumps_twist_by_deRham_character D P.T P.wd i (D.naut.iotaQC i) a ρ χ hρ hχ τ c (fun w hw => ?_) hc
    obtain ⟨h1, h2⟩ := h w hw
    exact ⟨(P.wdOf i a ρ w).2.2.2.1.1 h1, (P.wdOf i 1 χ w).2.2.2.1.1 h2⟩
  have pst : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) {b : ℕ} (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))),
      Continuous (fun g => ((r g : GL (Fin b) (Qbar (D.nd.l i))) : Matrix (Fin b) (Fin b) (Qbar (D.nd.l i)))) →
      D.naut.IsdRW i r w → ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
      (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) := by
    intro w hw b r hr hd O _ _ _ Bw hj
    exact hB.isPstAt (D.locT (D.nd.l i)) Bw _ (hr.comp continuous_subtype_val)
      ((GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) w hw O Bw hj b r hr).1 ((P.wdOf i b r w).2.2.2.1.1 hd))
  have p2 : ∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w) := by
    intro w h1 h2
    rw [(P.wdOf i a _ w).1, (P.wdOf i a ρ w).1, (P.wdOf i 1 χ w).1]
    have hd : D.naut.lpDim (P.wd.wdOf (D.nd.l i) (D.naut.iotaQC i) χ w) = 1 := P.wd.wdOf_dim _ _ χ w
    apply (P.T.e w).injective
    rw [P.T.char w _ _ hd]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d1 : D.naut.IsdRW i ρ w := h1.resolve_left (not_not.2 hw)
      have d2 : D.naut.IsdRW i χ w := h2.resolve_left (not_not.2 hw)
      have d3 := (p1 w hw d2).2 d1
      obtain ⟨L1, B1, j1, e1⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w hw
      obtain ⟨L2, B2, j2, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) ρ w hw
      obtain ⟨L3, B3, j3, e3⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) χ w hw
      rw [e1, e2, e3]
      have T0 : Nonempty (LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i))) := ⟨D.locT (D.nd.l i)⟩
      have hN := D.nbr_ind i w hw
      rw [GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B1 (D.nbr i w hw) j1 hN a _ (htc.comp continuous_subtype_val)
          (pst w hw _ htc d3 _ B1 j1) (pst w hw _ htc d3 _ (D.nbr i w hw) hN),
        GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B2 (D.nbr i w hw) j2 hN a _ (hρ.comp continuous_subtype_val)
          (pst w hw _ hρ d1 _ B2 j2) (pst w hw _ hρ d1 _ (D.nbr i w hw) hN),
        GlobalTheory.T.fontaineParameter_independent_of_localEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
          _ (D.nd.O i) B3 (D.nbr i w hw) j3 hN 1 _ (hχ.comp continuous_subtype_val)
          (pst w hw _ hχ d2 _ B3 j3) (pst w hw _ hχ d2 _ (D.nbr i w hw) hN)]
      have q3 := pst w hw _ htc d3 _ (D.nbr i w hw) hN
      rw [GlobalTheory.Pst.resDec, GlobalTheory.TwistGal.comp_twGL] at q3 ⊢
      exact GlobalTheory.T.fontaineParameter_twist_potentiallySemistable (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) T0 (D.naut.iotaQC i) D.host.E D.nd.Om _ w (D.nd.plOm.2 w)
        (D.nd.O i) (D.nbr i w hw) hN a _ _ (hρ.comp continuous_subtype_val) (hχ.comp continuous_subtype_val)
        (pst w hw _ hρ d1 _ (D.nbr i w hw) hN) (pst w hw _ hχ d2 _ (D.nbr i w hw) hN) q3
    · rw [P.wd.away _ _ _ w hw, P.wd.away _ _ _ w hw, P.wd.away _ _ _ w hw]
      exact GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l D.host.E D.nd.Om _ w (D.nd.plOm.2 w) (D.nd.l i) hw (D.naut.iotaQC i) a ρ χ hρ hχ
  exact ⟨p1, p2, p3⟩
end GlobalTheory.TwistGal
end
end
