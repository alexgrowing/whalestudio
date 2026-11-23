import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.GlobalFields.TateThesis.TraceDualLattice

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem eq_exp_of_le_of_not_le {a : ℤᵐ⁰} {n : ℤ} (h1 : a ≤ exp n) (h2 : ¬ a ≤ exp (n - 1)) :
    a = exp n := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact h2 zero_le
  rw [← exp_log ha] at h1 h2 ⊢
  rw [exp_le_exp] at h1 h2
  rw [exp_inj]
  omega

theorem coe_differentIdeal_ne_zero :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact differentIdeal_ne_bot

theorem intValuation_le_of_mem_ideal (v : HeightOneSpectrum (𝓞 K)) {𝔞 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥)
    {y : 𝓞 K} (hy : y ∈ 𝔞) :
    v.intValuation y ≤ exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [FractionalIdeal.count_coe K v h𝔞]
  refine (v.intValuation_le_pow_iff_mem y _).mpr ?_
  have hle := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔞)
      v.associates_irreducible (k := (Associates.mk v.asIdeal).count (Associates.mk 𝔞).factors)).mpr
      le_rfl
  rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le] at hle
  exact hle hy

theorem exists_mem_ideal_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ y ∈ 𝔞,
      v.intValuation y = exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk 𝔞).factors with hn
  have hnot : ¬ 𝔞 ≤ v.asIdeal ^ (n + 1) := by
    intro h
    have h' := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔞)
      v.associates_irreducible (k := n + 1)).not
    rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le] at h'
    exact h'.mpr (by omega) h
  obtain ⟨y, hy, hyn⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨y, hy, eq_exp_of_le_of_not_le (intValuation_le_of_mem_ideal v h𝔞 hy) fun h ↦ hyn ?_⟩
  rw [← v.intValuation_le_pow_iff_mem]
  convert h using 2
  rw [FractionalIdeal.count_coe K v h𝔞, ← hn]
  push_cast
  ring

theorem mem_localInvDifferent_iff_valued (v : HeightOneSpectrum (𝓞 K)) (z : v.adicCompletion K) :
    z ∈ localInvDifferent v ↔ Valued.v z ≤
      exp (FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)) := by
  set δ := FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)
  constructor
  · intro h
    obtain ⟨y, hy, hyv⟩ := exists_mem_ideal_intValuation_eq v (differentIdeal_ne_bot (A := ℤ))
    have h1 := h y hy
    rw [mem_adicCompletionIntegers, Valuation.map_mul, valued_coe_algebraMap, hyv] at h1
    calc Valued.v z = Valued.v z * exp (-δ) * exp δ := by
            rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
      _ ≤ 1 * exp δ := by gcongr
      _ = exp δ := one_mul _
  · intro h y hy
    rw [mem_adicCompletionIntegers, Valuation.map_mul, valued_coe_algebraMap]
    calc Valued.v z * v.intValuation y ≤ exp δ * exp (-δ) :=
          mul_le_mul' h (intValuation_le_of_mem_ideal v (differentIdeal_ne_bot (A := ℤ)) hy)
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

variable (K) in

def finiteAdelicChar : AddChar 𝔸ᶠ[K] Circle :=
  (adelicChar K).compAddMonoidHom finiteAdeleInr

theorem finiteAdelicChar_apply (x : 𝔸ᶠ[K]) :
    finiteAdelicChar K x = adelicChar K (finiteAdeleInr x) := rfl

theorem continuous_finiteAdelicChar : Continuous (finiteAdelicChar K) :=
  (continuous_adelicChar (K := K)).comp (continuous_const.prodMk continuous_id)

theorem finiteAdelicChar_eq_one_of_mem {x : 𝔸ᶠ[K]} (hx : x ∈ finiteInvDifferent K) :
    finiteAdelicChar K x = 1 := by
  rw [finiteAdelicChar_apply, adelicChar_of_mem_invDifferentAdeles
    (mem_invDifferentAdeles.mpr (by rw [finiteAdeleInr_snd]; exact hx)),
    finiteAdeleInr_fst, map_zero, neg_zero, AddChar.map_zero_eq_one]

theorem finiteAdelicChar_finiteAdeleSingleAdd (v : HeightOneSpectrum (𝓞 K))
    (w : v.adicCompletion K) :
    finiteAdelicChar K (finiteAdeleSingleAdd v w) = localAdelicChar K v w := rfl

theorem finiteAdeleSingleAdd_mul (v : HeightOneSpectrum (𝓞 K)) (w : v.adicCompletion K)
    (y : 𝔸ᶠ[K]) : finiteAdeleSingleAdd v w * y = finiteAdeleSingleAdd v (w * y v) := by
  refine Subtype.ext (funext fun u ↦ ?_)
  change finiteAdeleSingleAdd v w u * y u = finiteAdeleSingleAdd v (w * y v) u
  rcases eq_or_ne u v with rfl | hu
  · rw [finiteAdeleSingleAdd_apply_self, finiteAdeleSingleAdd_apply_self]
  · rw [finiteAdeleSingleAdd_apply_of_ne hu, finiteAdeleSingleAdd_apply_of_ne hu, zero_mul]

theorem count_traceDualIdeal (v : HeightOneSpectrum (𝓞 K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.count K v (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      -(FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) +
        FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [traceDualIdeal_eq, FractionalIdeal.count_inv,
    FractionalIdeal.count_mul K v I.ne_zero coe_differentIdeal_ne_zero]

theorem forall_finiteAdelicChar_mul_eq_one_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : 𝔸ᶠ[K]) :
    (∀ x ∈ idealFiniteAdeles I, finiteAdelicChar K (x * y) = 1) ↔
      y ∈ idealFiniteAdeles (traceDualIdeal K I) := by
  simp only [mem_idealFiniteAdeles, count_traceDualIdeal, neg_neg]
  constructor
  · intro h v
    set i := FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)
    set δ := FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K)
    set t : v.adicCompletion K := ((uniformizerUnit v ^ i : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) with ht
    have htv : Valued.v t = exp (-i) := valued_uniformizerUnit_zpow v i
    have hloc : t * y v ∈ localInvDifferent v := by
      refine (forall_localAdelicChar_mul_eq_one_iff v _).mp fun a ha ↦ ?_
      have hx : finiteAdeleSingleAdd v (a * t) ∈ idealFiniteAdeles I := by
        intro u
        rcases eq_or_ne u v with rfl | hu
        · rw [finiteAdeleSingleAdd_apply_self, Valuation.map_mul, htv]
          exact mul_le_of_le_one_left' ((mem_adicCompletionIntegers _ _ _).mp ha)
        · rw [finiteAdeleSingleAdd_apply_of_ne hu, Valuation.map_zero]
          exact zero_le
      have := h _ hx
      rwa [finiteAdeleSingleAdd_mul, finiteAdelicChar_finiteAdeleSingleAdd, mul_assoc] at this
    rw [mem_localInvDifferent_iff_valued, Valuation.map_mul, htv] at hloc
    calc Valued.v (y v) = exp i * (exp (-i) * Valued.v (y v)) := by
            rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ ≤ exp i * exp δ := by gcongr
      _ = exp (i + δ) := by rw [exp_add]
  · intro hy x hx
    refine finiteAdelicChar_eq_one_of_mem fun v ↦ ?_
    change x v * y v ∈ localInvDifferent v
    rw [mem_localInvDifferent_iff_valued, Valuation.map_mul]
    calc Valued.v (x v) * Valued.v (y v) ≤
          exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) *
            exp (FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) +
              FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
                FractionalIdeal (𝓞 K)⁰ K)) := mul_le_mul' (hx v) (hy v)
      _ = _ := by rw [← exp_add, neg_add_cancel_left]

theorem traceDualIdeal_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualIdeal K (traceDualIdeal K I) = I :=
  Units.ext (FractionalIdeal.dual_dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))

theorem finiteAdeleMeasure_idealFiniteAdeles_toReal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (finiteAdeleMeasure K (idealFiniteAdeles I)).toReal =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ))⁻¹ *
        (NNReal.sqrt ‖discr K‖₊ : ℝ)⁻¹ := by
  rw [finiteAdeleMeasure_idealFiniteAdeles, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (inv_nonneg.mpr (by exact_mod_cast (FractionalIdeal.absNorm_nonneg _))),
    ENNReal.coe_toReal, NNReal.coe_inv]

theorem finiteAdeleMeasure_idealFiniteAdeles_ne_top (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    finiteAdeleMeasure K (idealFiniteAdeles I) ≠ ∞ := by
  rw [finiteAdeleMeasure_idealFiniteAdeles]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top

theorem finiteAdeleMeasure_idealFiniteAdeles_mul_traceDual (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (finiteAdeleMeasure K (idealFiniteAdeles I)).toReal *
      (finiteAdeleMeasure K (idealFiniteAdeles (traceDualIdeal K I))).toReal = 1 := by
  rw [finiteAdeleMeasure_idealFiniteAdeles_toReal, finiteAdeleMeasure_idealFiniteAdeles_toReal,
    traceDualIdeal_eq, map_inv₀, map_mul, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal K (𝓞 K)]
  have hN : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hs : ((NNReal.sqrt ‖discr K‖₊ : ℝ)) ^ 2 = ((discr K).natAbs : ℝ) := by
    rw [← NNReal.coe_pow, NNReal.sq_sqrt, coe_nnnorm, Int.norm_eq_abs, Nat.cast_natAbs,
      Int.cast_abs]
  have hs0 : (NNReal.sqrt ‖discr K‖₊ : ℝ) ≠ 0 := by
    exact_mod_cast sqrt_discr_ne_zero K
  generalize (NNReal.sqrt ‖discr K‖₊ : ℝ) = s at hs hs0 ⊢
  generalize (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) = N at hN ⊢
  rw [Rat.cast_inv, Rat.cast_mul, Rat.cast_natCast, ← hs]
  field_simp

end

end GroundTheory.Global
