import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorRightEdgeCosine
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorRightEdgeCosineStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.CosetRow in
theorem GlobalTheory.CosetRow.coset_function_isLocalVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsLocVec ch.W (.chi i 0) e (ch.rm.vX i 0) (GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.right i 0)) (ch.W.cosVec i (Φ i)) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi _ => ?_⟩⟩
  intro t e he Φ i
  classical
  have hL := s.core.lev
  obtain ⟨e₀, he₀, hcv⟩ := ch.W.cosVec_is
  obtain ⟨he₁, h01⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he₀ Finset.subset_union_left
  have hee : e₀ + (e - e₀) = e := add_sub_cancel e₀ e
  have hAA : ∀ w ∈ R.toLevCh.Q t, w ∉ ch.G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    refine GlobalTheory.T.host_ideal_unit_at_places_prime_to_level D w (fun h => (hL.Q_off t w hw).1 ?_) (fun h => s.guard.2 t w hw ?_)
    · rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h
    · rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h
  rw [GlobalTheory.T.givenStageFunction_rowArrow_eq_halfExtension hL ch.S.B t Φ he he₀ hAA i, ch.rm.vX_row]
  obtain ⟨dS, dT⟩ := selfDual_chi hL ch.G i i.2
  have h0 := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd dS dT (ch.G.pl.modul_ne_bot _) h0 (GlobalTheory.PlaceDatum.infPart_idemSum he₀) (Φ i)
  have hex := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ch.W.ψ ch.W.ψ_std _ _ _ _ dS dT _ e he _
    (ch.W.vac_is i i.2).2.theta (ch.W.vac_is i i.2).2.lat).1
  rw [← hee] at hex
  have key : IsLocVec ch.W (.chi i 0) (e₀ + (e - e₀)) (ch.W.vac i)
      (extFn e₀ (e - e₀) (latO (ch.G.pS (.chi (i : ℕ) 0)) (ch.G.pT (.chi (i : ℕ) 0)) (ch.G.latS (.chi (i : ℕ) 0) : Set _)
        (ch.G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i))) (ch.W.cosVec i (Φ i)) :=
    ⟨GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn h0 h1 h01 (fun _ hu => smul_mem_latO_idem _ _ h0 hu) (fun _ hu => smul_mem_latO_idem _ _ h1 hu) hSB,
      GlobalTheory.T.isThetaAt_halfExtensionLatticeIndicatorFn h0 h1 h01 (fun _ hu => smul_mem_latO_idem _ _ h0 hu) (fun _ hu => smul_mem_latO_idem _ _ h1 hu)
        (fun t y ht hy => symplO_eq_of_half h01 t y ht hy) hex (hcv i i.2 (Φ i))⟩
  rwa [hee] at key
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_coset_function_isLocalVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsLocVec ch.W (.chi i 0) e (ch.rm.vX i 0) (GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.right i 0)) (ch.W.cosVec i (Φ i)) := by
  first | exact @_root_.GlobalTheory.CosetRow.coset_function_isLocalVector | exact _root_.GlobalTheory.CosetRow.coset_function_isLocalVector | (intros; apply _root_.GlobalTheory.CosetRow.coset_function_isLocalVector <;> assumption)
end
