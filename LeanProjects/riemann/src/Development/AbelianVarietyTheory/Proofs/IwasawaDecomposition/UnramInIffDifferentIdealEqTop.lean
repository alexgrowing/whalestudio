import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.UnramDiscr

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem not_dvd_iff_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) ↔ P.inertia (L ≃ₐ[K] L) = ⊥ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  rw [not_dvd_differentIdeal_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P,
    Subgroup.card_eq_one]

theorem unramIn_iff_differentIdeal_eq_top :
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔ differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  unfold UnramIn InInertia
  constructor
  · intro h
    by_contra hD
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hD
    haveI := hM
    have hMb : M ≠ ⊥ := by
      rintro rfl
      exact hD0 (le_bot_iff.mp hDM)
    have hMu : M.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hMb
    have hb : M.inertia (L ≃ₐ[K] L) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      exact h ⟨M.under (𝓞 K), inferInstance, hMu⟩ σ ⟨M, inferInstance, ⟨rfl⟩, fun x => hσ x⟩
    exact (not_dvd_iff_inertia K L M hMb).mpr hb (Ideal.dvd_iff_le.mpr hDM)
  · rintro hD 𝔭 σ ⟨P, hP, hPo, hσ⟩
    haveI := hP
    haveI := hPo
    have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
    have hnd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
      rw [hD]
      exact fun hd => hP.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hd))
    have hb := (not_dvd_iff_inertia K L P hPb).mp hnd
    have hmem : σ ∈ P.inertia (L ≃ₐ[K] L) := fun x => hσ x
    rw [hb] at hmem
    exact Subgroup.mem_bot.mp hmem

omit K L in

theorem unramIn_iff_natAbs_discr :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔
        (discr L).natAbs = (discr K).natAbs ^ Module.finrank K L := by
  intro K L _ _ _ _ _ _
  rw [unramIn_iff_differentIdeal_eq_top K L,
    natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  have h0 : 0 < (discr K).natAbs ^ Module.finrank K L :=
    pow_pos (Int.natAbs_pos.mpr (discr_ne_zero K)) _
  constructor
  · intro h
    rw [h, Ideal.absNorm_top, one_mul]
  · intro h
    apply Ideal.absNorm_eq_one_iff.mp
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [h, one_mul]

end GlobalTheory.UnramDiscr
