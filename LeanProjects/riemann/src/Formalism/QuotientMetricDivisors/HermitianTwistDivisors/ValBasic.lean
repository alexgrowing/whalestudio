import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationRepresentative

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cO_apply (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_apply, cO_apply, star_star]

theorem map_cO_map_cO (I : Ideal (𝓞 K)) : (I.map (cO K)).map (cO K) = I := by
  ext y
  simp only [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rwa [cO_cO]
  · intro hy
    exact ⟨cO K y, ⟨y, hy, rfl⟩, cO_cO y⟩

theorem conjPl_conjPl (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := HeightOneSpectrum.ext (map_cO_map_cO w.asIdeal)

theorem map_cO_le_iff (I J : Ideal (𝓞 K)) : I.map (cO K) ≤ J.map (cO K) ↔ I ≤ J := by
  constructor
  · intro h
    have h2 := Ideal.map_mono (f := cO K) h
    rwa [map_cO_map_cO, map_cO_map_cO] at h2
  · intro h
    exact Ideal.map_mono (f := cO K) h

theorem dvd_map_iff (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (n : ℕ) :
    (v.asIdeal.map (cO K)) ^ n ∣ J.map (cO K) ↔ v.asIdeal ^ n ∣ J := by
  rw [← Ideal.map_pow, Ideal.dvd_iff_le, Ideal.dvd_iff_le, map_cO_le_iff]

theorem count_map (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    FractionalIdeal.count K (conjPl v) ((J.map (cO K) : Ideal (𝓞 K)) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
    FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have hJ' : J.map (cO K) ≠ 0 := fun h =>
    hJ ((Ideal.map_eq_bot_iff_of_injective (cO K).injective).mp h)
  rw [FractionalIdeal.count_coe K (conjPl v) hJ', FractionalIdeal.count_coe K v hJ]
  congr 1
  apply eq_of_forall_le_iff
  intro n
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ')
      (Associates.irreducible_mk.mpr (conjPl v).irreducible),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
      (Associates.irreducible_mk.mpr v.irreducible),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd]
  exact dvd_map_iff v J n

theorem vw_zero (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by
  simp only [vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]

theorem vw_mul (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) b ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K w h1 h2

theorem vw_inv (w : HeightOneSpectrum (𝓞 K)) (a : K) : vw w a⁻¹ = - vw w a := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem vw_one (w : HeightOneSpectrum (𝓞 K)) : vw w (1 : K) = 0 := by
  simp only [vw]
  rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem vw_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (x : K) = FractionalIdeal.count K w
      ((Ideal.span {x} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  rw [FractionalIdeal.coeIdeal_span_singleton]
  rfl

theorem vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) : 0 ≤ vw w (x : K) := by
  rw [vw_int]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_star_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (star (x : K)) = vw (conjPl w) (x : K) := by
  by_cases hx : x = 0
  · subst hx
    simp [vw_zero]
  · have hJ : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have key := count_map (conjPl w) (Ideal.span {x}) hJ
    rw [conjPl_conjPl] at key
    rw [← cO_apply, vw_int, vw_int, ← key, Ideal.map_span, Set.image_singleton]

private theorem vw_div (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a / b) = vw w a - vw w b := by
  rw [div_eq_mul_inv, vw_mul w a b⁻¹ ha (inv_ne_zero hb), vw_inv, sub_eq_add_neg]

theorem vw_star (w : HeightOneSpectrum (𝓞 K)) (a : K) :
    vw w (star a) = vw (conjPl w) a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have e : ∀ z : 𝓞 K, algebraMap (𝓞 K) K z = (z : K) := fun _ => rfl
  have hy0 : (y : K) ≠ 0 := by
    rw [Ne, ← e, ← map_zero (algebraMap (𝓞 K) K)]
    exact (IsFractionRing.injective (𝓞 K) K).ne (nonZeroDivisors.ne_zero hy)
  rw [e, e]
  by_cases hx0 : (x : K) = 0
  · rw [hx0, zero_div, star_zero, vw_zero, vw_zero]
  · rw [star_div₀, vw_div w _ _ (star_ne_zero.mpr hx0) (star_ne_zero.mpr hy0),
      vw_div _ _ _ hx0 hy0, vw_star_int, vw_star_int]

theorem absNorm_map_ringEquiv {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] (g : S ≃+* S) (I : Ideal S) :
    Ideal.absNorm (I.map g) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map g) g rfl).toEquiv).symm

theorem lw_conjPl (w : HeightOneSpectrum (𝓞 K)) : lw (conjPl w) = lw w := by
  unfold lw
  rw [show (conjPl w).asIdeal = w.asIdeal.map (cO K) from rfl, absNorm_map_ringEquiv]

theorem gramR_eq {K : Type} [Field K] [StarRing K] {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) :
    gramR Γ e = ((Matrix.of e).map star * Γ * (Matrix.of e).transpose).det := by
  unfold gramR
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end ValuationRepresentative

open ValuationRepresentative

theorem valuation_basic_properties : ValBasic := by
  intro K _ _ _ w
  exact ⟨fun a b ha hb => vw_mul w a b ha hb, vw_star w, lw_conjPl w, conjPl_conjPl w,
    vw_one w, vw_inv w, vw_int_nonneg w⟩

theorem gram_matrix_change : GramChange := by
  intro K _ _ D m Γ e γ
  have h : Matrix.of (fun i => ∑ k, γ k i • e k) = γᵀ * Matrix.of e := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hm : (γᵀ * Matrix.of e).map star = γᵀ.map star * (Matrix.of e).map star := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      star_sum, star_mul']
  have hd : (γᵀ.map star).det = star γ.det := Matrix.det_conjTranspose γ
  have hr : γᵀ.map star * (Matrix.of e).map star * Γ * ((Matrix.of e)ᵀ * γ) =
      γᵀ.map star * ((Matrix.of e).map star * Γ * (Matrix.of e)ᵀ) * γ := by
    simp only [Matrix.mul_assoc]
  rw [gramR_eq, gramR_eq, h, hm, Matrix.transpose_mul, Matrix.transpose_transpose, hr,
    Matrix.det_mul, Matrix.det_mul, hd]
  ring

theorem finite_sum_conjugation : FinsumConj := by
  intro K _ _ _ f
  exact finsum_comp_equiv (Function.Involutive.toPerm _ (fun w => conjPl_conjPl w))

end Formalism.DivisionValues
