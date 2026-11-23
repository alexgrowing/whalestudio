import Mathlib
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.Artin.SeriesEuler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField

noncomputable section

section Average

variable {G : Type*} [Group G]

open Classical in

theorem cosetAverage_character (I : Subgroup G) [Finite I] (χ : G →* ℂˣ) (g : G) :
    cosetAverage I (fun x ↦ (χ x : ℂ)) g = if ∀ i ∈ I, χ i = 1 then (χ g : ℂ) else 0 := by
  have := Fintype.ofFinite I
  rw [cosetAverage_eq_sum]
  simp only [map_mul, Units.val_mul]
  rw [← Finset.mul_sum]
  split_ifs with h
  · have hs : ∑ i : I, ((χ i : ℂˣ) : ℂ) = Nat.card I := by
      rw [Finset.sum_congr rfl fun i _ ↦ by rw [h i i.2, Units.val_one], Finset.sum_const,
        Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
    have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [hs, mul_left_comm, inv_mul_cancel₀ hI, mul_one]
  · let ψ : I →* ℂ := (Units.coeHom ℂ).comp (χ.comp I.subtype)
    have hψ : ψ ≠ 1 := by
      intro h1
      apply h
      intro i hi
      have := DFunLike.congr_fun h1 ⟨i, hi⟩
      exact Units.val_eq_one.1 this
    have hs : ∑ i : I, ((χ i : ℂˣ) : ℂ) = 0 := sum_hom_units_eq_zero ψ hψ
    rw [hs, mul_zero, mul_zero]

end Average

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

open Classical in

theorem artinLocalLog_character (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    artinLocalLog K L (fun g ↦ (χ g : ℂ)) s v =
      if ∀ σ ∈ (placeAbove (L := L) v).asIdeal.inertia Gal(L/K), χ σ = 1 then
        -Complex.log (1 - χ (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      else 0 := by
  have hterm : ∀ m, artinTerm K L (fun g ↦ (χ g : ℂ)) s v m =
      if ∀ σ ∈ (placeAbove (L := L) v).asIdeal.inertia Gal(L/K), χ σ = 1 then
        (χ (arithFrobAt (𝓞 K) Gal(L/K) (placeAbove (L := L) v).asIdeal) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ m / m
      else 0 := fun m ↦ by
    rw [artinTerm, localAverage, cosetAverage_character]
    split_ifs
    · rw [map_pow, Units.val_pow_eq_pow_val, mul_pow]
    · rw [zero_mul, zero_div]
  rw [artinLocalLog, tsum_congr hterm]
  split_ifs
  · refine (Complex.hasSum_taylorSeries_neg_log ?_).tsum_eq
    rw [norm_mul, norm_coe_apply_eq_one, one_mul]
    exact norm_absNorm_cpow_neg_lt_one v hs
  · exact tsum_zero

theorem artinL_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    artinL K L (fun g ↦ (χ g : ℂ)) s = (heckeCharacterOfChar χ).LFunction s := by
  have h1 : HasProd (Complex.exp ∘ fun v ↦ artinLocalLog K L (fun g ↦ (χ g : ℂ)) s v)
      (artinL K L (fun g ↦ (χ g : ℂ)) s) :=
    (hasSum_artinLocalLog_artinLogL _ hs).cexp
  refine h1.unique ?_
  convert (heckeCharacterOfChar χ).LFunction_hasProd_all hs using 1
  funext v
  rw [Function.comp_apply, artinLocalLog_character χ v hs]
  set w := placeAbove (L := L) v
  split_ifs with hχ
  · have hv := (not_dvd_conductor_heckeCharacterOfChar_iff χ v w).2 hχ
    obtain ⟨π, -, hπ⟩ := exists_ord_eq_one_valued v
    have hc : (heckeCharacterOfChar χ).coeff v.asIdeal =
        χ (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) := by
      rw [HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv,
        HeckeCharacter.idealCharacter_primeIdealUnit _ hv hπ,
        localComponent_uniformizer χ v w hχ hπ (IsArithFrobAt.arithFrobAt _ _ _)]
    have hne : 1 - (χ (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := by
      intro h
      have h2 : ‖(χ (arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal) : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
        rw [norm_mul, norm_coe_apply_eq_one, one_mul]
        exact norm_absNorm_cpow_neg_lt_one v hs
      rw [← sub_eq_zero.1 h, norm_one] at h2
      exact lt_irrefl _ h2
    rw [hc, Complex.exp_neg, Complex.exp_log hne]
  · have hv : v.asIdeal ∣ (heckeCharacterOfChar χ).conductor :=
      not_not.1 fun h ↦ hχ ((not_dvd_conductor_heckeCharacterOfChar_iff χ v w).1 h)
    rw [HeckeCharacter.coeff_asIdeal_of_dvd _ hv, zero_mul, sub_zero, inv_one, Complex.exp_zero]

end

end GroundTheory.Global
