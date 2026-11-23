import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuadCharOfOfIsNormChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationEqOfIneFixes

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.QuadNormRam

theorem not_unrAt_of_ramified : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M],
    Module.finrank K M = 2 → ∀ η : HChar K, IsNormChar M η → ∀ w : HeightOneSpectrum (𝓞 M),
    ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal → ¬ η.UnrAt (w.under (𝓞 K)) := by
  intro F E _ _ _ _ _ h2 η hη w hram hu
  have hGAR : GlobalTheory.Published.GlobalArtinReciprocity := GlobalTheory.globalArtinReciprocity_holds
  obtain ⟨hne, hpow, hsplit⟩ := hη
  rw [h2] at hpow
  let Ω := AlgebraicClosure E
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨artF, haF⟩ := hGAR F Ω
  obtain ⟨artE, haE⟩ := hGAR E Ω
  obtain ⟨δ, hδc, hL⟩ := haF.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) (m := 2) (by norm_num) hpow)
  have hEig : ∀ v : HeightOneSpectrum (𝓞 F), η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := by
    intro v hu A hA
    refine ⟨fun s hs => (hL.unr_iff haF (Or.inr rfl) hA).2 hu s hs, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr haF (Or.inr rfl) hu hA hσ, inv_inv, ι.apply_symm_apply]
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, η.UnrAt (w.under (𝓞 F)) ∧
      ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1 :=
    ((GlobalTheory.QuadNormChar.tendsto_under (K := F) (K' := E)).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))).and hsplit
  have hres : δ.comp (res F Ω E) = 1 := by
    have hS := Filter.eventually_cofinite.1 hev
    refine GlobalTheory.FrobDense.eq_one_of_frob E Ω artE haE (Qbar 2)ˣ _
      (hδc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom F E Ω)) hS.toFinset fun w hw A hA σ hσ => ?_
    have hw' : η.UnrAt (w.under (𝓞 F)) ∧
        ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1 := by
      simpa using hw
    have hf := GlobalTheory.QuadNormChar.normV_under (K := F) w
    have h1 := ((UpperTheory.frobenius_power_compatibility F E Ω 2 ι w _ hf).2 δ _ (hEig _ hw'.1)) A hA
    have h3 := h1.2 σ hσ
    rw [← Units.val_pow_eq_pow_val, hw'.2 _ hf, Units.val_one, map_eq_one_iff _ ι.injective,
      Units.val_eq_one, map_inv, inv_eq_one] at h3
    exact h3

  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  have hAv : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)

  have hmove : ∃ s ∈ Ine (F := F) A, ∃ e : E, s (algebraMap E Ω e) ≠ algebraMap E Ω e := by
    by_contra hfix
    push_neg at hfix
    obtain ⟨hlo, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 F)) w hAv hA hfix
    exact hram (Ideal.ramificationIdx_eq_one_iff.1 he)
  obtain ⟨s, hs, hsm⟩ := hmove
  have hδs : δ s = 1 := (hL.unr_iff haF (Or.inr rfl) hAv).2 hu s hs
  have hδ1 : δ = 1 := MonoidHom.ext fun τ => by
    rcases GlobalTheory.QuadNormChar.fixes_or h2 s hsm τ with ⟨τ', rfl⟩ | ⟨τ', hτ'⟩
    · exact DFunLike.congr_fun hres τ'
    · have := DFunLike.congr_fun hres τ'
      rw [MonoidHom.comp_apply, hτ', map_mul, map_inv, hδs, inv_one, one_mul] at this
      exact this
  apply hne
  apply Subtype.ext
  refine MonoidHom.ext fun x => Units.ext ?_
  obtain ⟨τ, hτ⟩ := toAb_surjective (artF x)
  have := hL x τ hτ.symm
  rw [hδ1, infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
    map_eq_one_iff _ ι.symm.injective] at this
  exact this

end GlobalTheory.QuadNormRam
