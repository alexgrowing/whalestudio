import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.V.Af.Bc
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam :
    NormRam := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ hp η hη A v hA hτ hunr
  obtain ⟨τ, hτI, hτM⟩ := hτ
  obtain ⟨hη1, hηp, hηev⟩ := hη
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have halg : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd hp.pos hηp
  obtain ⟨r, hrc, hr⟩ := hart.exists_isLAdicOf (ι : Qbar 2 ≃+* ℂ) halg
  have hrI : ∀ s ∈ Ine A, r s = 1 := (hr.unr_iff hart (Or.inr rfl) hA).2 hunr
  have hres : ∀ g : G M Ω, r (res K Ω M g) = 1 := by
    haveI : IsAlgClosure M Ω := by
      haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
      exact ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) M⟩
    obtain ⟨artM, hartM⟩ := GlobalTheory.globalArtinReciprocity_holds M Ω
    have hφc : Continuous (r.comp (res K Ω M)) :=
      hrc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K M Ω)
    have hbad : {w : HeightOneSpectrum (𝓞 M) | ¬ (η.UnrAt (HeightOneSpectrum.under (𝓞 K) w) ∧
        ∀ f : ℕ, normV w = normV (HeightOneSpectrum.under (𝓞 K) w) ^ f →
          η.val (HeightOneSpectrum.under (𝓞 K) w) ^ f = 1)}.Finite := by
      have h1 := GlobalTheory.QuadNormChar.tendsto_under (K := K) (K' := M)
      have h2 : ∀ᶠ w in Filter.cofinite, η.UnrAt (HeightOneSpectrum.under (𝓞 K) w) :=
        h1.eventually (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))
      exact Filter.eventually_cofinite.1 (h2.and hηev)
    have hone := GlobalTheory.FrobDense.eq_one_of_frob M Ω artM hartM (Qbar 2)ˣ (r.comp (res K Ω M)) hφc
      hbad.toFinset ?_
    · intro g
      exact DFunLike.congr_fun hone g
    · intro w hw A' hA' σ hσ
      rw [Set.Finite.mem_toFinset] at hw
      simp only [Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hwu, hwn⟩ := hw
      have hce : CharEig ι r (HeightOneSpectrum.under (𝓞 K) w)
          (η.val (HeightOneSpectrum.under (𝓞 K) w)) := by
        intro B hB
        refine ⟨(hr.unr_iff hart (Or.inr rfl) hB).2 hwu, fun σ' hσ' => ?_⟩
        have h3 := hr.frob_unr hart (Or.inr rfl) hwu hB hσ'
        rw [map_inv, Units.val_inv_eq_inv_val, h3, inv_inv]
        simp
      obtain ⟨-, hfr⟩ := UpperTheory.frobenius_power_compatibility K M Ω 2 ι w (w.asIdeal.inertiaDeg (𝓞 K))
        (GlobalTheory.QuadNormChar.normV_under w)
      obtain ⟨-, hval⟩ := hfr r _ hce A' hA'
      have h6 := hval σ hσ
      have h7 : ((η.val (HeightOneSpectrum.under (𝓞 K) w) : ℂˣ) : ℂ) ^
          (w.asIdeal.inertiaDeg (𝓞 K)) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hwn _ (GlobalTheory.QuadNormChar.normV_under w)]
        rfl
      rw [h7] at h6
      have h8 : (((r.comp (res K Ω M)) σ⁻¹ : (Qbar 2)ˣ) : Qbar 2) = 1 := by
        have h9 := congrArg ι.symm h6
        simpa using h9
      have h10 : (r.comp (res K Ω M)) σ⁻¹ = 1 := Units.ext h8
      rw [map_inv, inv_eq_one] at h10
      exact h10
  have hr1 : ∀ g : G K Ω, r g = 1 := by
    haveI : Fact (Nat.Prime (Module.finrank K M)) := ⟨hp⟩
    let ρ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
    have hfix : ∀ g : G K Ω, ρ g = 1 → r g = 1 := by
      intro g hg
      let g' : Ω ≃ₐ[M] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
        have h1 := AlgEquiv.restrictNormal_commutes g M x
        have h2 : g.restrictNormal M = 1 := hg
        rw [h2] at h1
        simpa using h1.symm)
      have hg' : res K Ω M g' = g := by
        ext x
        rfl
      rw [← hg']
      exact hres g'
    have hρτ : ρ τ ≠ 1 := by
      intro h1
      apply hτM
      intro x
      have h3 := AlgEquiv.restrictNormal_commutes τ M x
      have h2 : τ.restrictNormal M = 1 := h1
      rw [h2] at h3
      simpa using h3.symm
    have hgen : Subgroup.zpowers (ρ τ) = ⊤ :=
      zpowers_eq_top_of_prime_card (p := Module.finrank K M)
        (IsGalois.card_aut_eq_finrank K M) hρτ
    intro g
    have hg : ρ g ∈ Subgroup.zpowers (ρ τ) := hgen ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hτ1 : r τ = 1 := hrI τ hτI
    have h4 : ρ ((τ ^ k)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    have h5 := hfix _ h4
    rw [map_mul, map_inv, map_zpow, hτ1, one_zpow, inv_one, one_mul] at h5
    exact h5
  apply hη1
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
  have h := hr x σ hσ.symm
  rw [infPow_zero, lPow_zero, hr1 σ] at h
  simp only [Units.val_one, inv_one, mul_one] at h
  have h2 : ((η.1 x : ℂˣ) : ℂ) = 1 := by
    have h3 := congrArg ι h
    simpa using h3.symm
  ext
  simpa using h2
