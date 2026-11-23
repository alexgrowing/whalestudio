import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatK

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.ThetaPull
namespace UpperTheory.V.Af
private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)
private theorem sep_theta {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} {π π' : CuspSub K n} {σ : ℂ ≃+* ℂ}
    (hc : π.IsCsd) (h : Sep σ π.finPart π'.finPart) (h' : Sep σ.symm π'.finPart π.finPart) :
    Sep (RingEquiv.refl ℂ) π'.finPart (thetaSub π').finPart ∧ Sep (RingEquiv.refl ℂ) (thetaSub π').finPart π'.finPart := by
  obtain ⟨T, hT⟩ := hc
  have h1 := Sep.of_equiv (ρ := π.finPart.comp (thetaGL n (cFin K))) (ρ' := π.finPart) T fun g v => hT (.fin g) v
  have h2 := Sep.of_equiv (ρ := π'.finPart.comp (thetaGL n (cFin K))) (ρ' := (thetaSub π').finPart)
    ((pull K n).submoduleMap π'.V) fun g v => Subtype.ext (act_pull (.fin g) v.1).symm
  have e : σ.symm.trans σ = RingEquiv.refl ℂ := σ.symm_trans_self
  exact ⟨e ▸ ((h'.trans h1.2).trans (h.comp _)).trans h2.1, e ▸ ((h2.2.trans (h'.comp _)).trans h1.1).trans h⟩
end UpperTheory.V.Af
open UpperTheory.V.Af in
theorem UpperTheory.V.Af.conjK_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.ConjK := by
  intro P K _ _ _ n hn m hm M hM σ π ⟨hinf, hdual, hfix⟩
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π (regAlg_of_infOf hm hinf) σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hfix' := hs.hasFixed hfix
  refine ⟨π', ⟨fun φ => ?_, ?_, hfix'⟩, fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  · obtain ⟨ht, ht'⟩ := sep_theta (GlobalTheory.CsdBack.isCsd_of_paired P.litN.aut.fin K n π (P.litN.aut.gk K n π) hdual) hs hs'
    refine GlobalTheory.LocGlobDual.Model.dualIsConj_of_isCsd (P.litN.aut.gk K n π') (isCsd_of_iso (Quotient.exact
      (P.litN.aut.js.1.strong_multiplicity_one (by omega) (CG.mk (thetaSub π')) (CG.mk π') ?_)))
    refine (eventually_notMem hM).mono fun w hw => ?_
    obtain ⟨B, hB⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π' hfix' w hw
    exact ⟨B, (ht.comp _).hasSatGL_refl (ht'.comp _) hB, hB⟩
end
