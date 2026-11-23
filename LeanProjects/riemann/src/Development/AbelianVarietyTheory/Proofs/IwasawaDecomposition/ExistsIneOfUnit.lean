import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisensteinStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusInvMulMemInertiaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRatioPiCongrTameUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitPowNormVSubOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMemStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem GlobalTheory.TameRecip.exists_ine_of_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) → ∀ (x : (v.adicCompletion E)ˣ) (u : 𝓞 E), IsUnitAt v x → Valued.v ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) < 1 → ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = art (localIdele E v x) ∧ A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 := by
  intro H E Ω _ _ _ _ _ _ art ha v A hA ϖ hϖ1 hϖ2 π hπ x u hx hxu
  have hq : 1 < normV v := by
    unfold normV
    have : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    exact Finite.one_lt_card
  have hn : 0 < normV v - 1 := by omega
  have hvE : ∀ a : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (a : E)) = v.valuation E (a : E) :=
    fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hu1 : Valued.v (algebraMap E (v.adicCompletion E) (u : E)) = 1 := by
    rw [hvE]
    refine le_antisymm (v.valuation_le_one u) (not_lt.mp fun h => ?_)
    have hm : u ∈ v.asIdeal := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mp h
    have hlt : Valued.v (x : v.adicCompletion E) < 1 := by
      have e : (x : v.adicCompletion E) = ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) +
          algebraMap E (v.adicCompletion E) (u : E) := by ring
      rw [e]
      refine Valuation.map_add_lt _ hxu ?_
      rw [hvE]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
    rw [hx'] at hlt
    exact lt_irrefl _ hlt
  have hu : u ∉ v.asIdeal := by
    intro hm
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    rw [← hvE, hu1] at h
    exact lt_irrefl _ h
  have hu0 : algebraMap E (v.adicCompletion E) (u : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  let uc : (v.adicCompletion E)ˣ := Units.mk0 _ hu0
  have hy : Valued.v (((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) < 1 := by
    have e : ((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
        ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) *
          (algebraMap E (v.adicCompletion E) (u : E))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, uc, Units.val_mk0]
      field_simp
    rw [e, map_mul, map_inv₀, hu1, inv_one, mul_one]
    exact hxu
  obtain ⟨z, hz1, hz⟩ := GlobalTheory.T.exists_unit_pow_normV_sub_one' E v (x * uc⁻¹) hy
  obtain ⟨ρ, hρ, hρz⟩ := (ha.ine v A hA _).mp ⟨z, hz1, rfl⟩
  obtain ⟨τ, hτF, hτπ, hτc⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA ϖ hϖ1 hϖ2 π hπ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E)) hn
  have h1' : u * ϖ ∈ v.asIdeal := Ideal.mul_mem_left _ _ hϖ1
  have h2' : u * ϖ ∉ v.asIdeal ^ 2 := by
    intro h
    rcases Ideal.IsPrime.mul_mem_pow v.asIdeal h with h3 | h3
    · exact hu h3
    · exact hϖ2 h3
  have hπ' : (π * t) ^ (normV v - 1) = algebraMap E Ω ((u * ϖ : 𝓞 E) : E) := by
    rw [mul_pow, hπ, ht, ← map_mul]
    push_cast
    ring_nf
  obtain ⟨τ', hτ'F, hτ'π, hτ'c⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA (u * ϖ) h1' h2' (π * t) hπ'
  have hσ0 : τ'⁻¹ * τ ∈ Ine (F := E) A := GlobalTheory.T.frobenius_inv_mul_mem_inertia E Ω v A hA τ τ' hτF hτ'F
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 hπ
  have hval := GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit E Ω v A hA u hu π t hπ0 ht τ τ' hτF hτ'F hτπ hτ'π
  have hc0 : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ((map_ne_zero _).mpr hϖ0)
  have huE : (u : E) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hcast : ((u * ϖ : 𝓞 E) : E) = (u : E) * (ϖ : E) := by push_cast; ring
  have hs0 : ((-1) ^ normV v : v.adicCompletion E) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hϖc : algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hc0' : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (((u * ϖ : 𝓞 E)) : E) ≠ 0 := by
    rw [hcast, map_mul]
    exact mul_ne_zero hs0 (mul_ne_zero hu0 hϖc)
  have ec := hτc (Units.mk0 _ hc0) rfl
  have ec' := hτ'c (Units.mk0 _ hc0') rfl
  have hmain : toAb E Ω (τ'⁻¹ * τ) = art (localIdele E v uc) := by
    have e1 : toAb E Ω τ = (art (localIdele E v (Units.mk0 _ hc0)))⁻¹ := by
      rw [← ec, map_inv, inv_inv]
    rw [map_mul, ec', e1, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, uc]
    rw [hcast, map_mul]
    field_simp
  refine ⟨τ'⁻¹ * τ * ρ ^ (normV v - 1), mul_mem hσ0 (pow_mem hρ _), ?_, ?_⟩
  · rw [map_mul, map_pow, hmain, hρz, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hz]
    congr 1
    rw [mul_comm x, mul_inv_cancel_left]
  · have e : (τ'⁻¹ * τ * ρ ^ (normV v - 1)) π = (τ'⁻¹ * τ) π := by
      rw [AlgEquiv.mul_apply, GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem E Ω v A hA (ϖ : E) π hπ ρ hρ]
    rw [e]
    exact hval

end
