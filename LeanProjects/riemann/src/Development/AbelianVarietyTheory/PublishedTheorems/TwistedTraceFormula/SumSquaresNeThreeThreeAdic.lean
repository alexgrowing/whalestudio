import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HermLocal

namespace GlobalTheory.HermLocal.Model

section Quad
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]

noncomputable def conjSqrt : QuadraticAlgebra K d 0 ≃ₐ[K] QuadraticAlgebra K d 0 :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by
    change star _ = _
    ext <;> simp

theorem conjSqrt_apply (z : QuadraticAlgebra K d 0) : conjSqrt d z = star z := rfl

theorem conjSqrt_ne_one (h2 : (2 : K) ≠ 0) : conjSqrt d ≠ 1 := by
  intro h
  have := congrArg QuadraticAlgebra.im (DFunLike.congr_fun h QuadraticAlgebra.omega)
  simp [conjSqrt_apply] at this
  exact h2 (by linear_combination -this)

theorem isQuadratic : Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two d 0

end Quad

instance two_not_sq : Fact (∀ r : ℚ_[2], r ^ 2 ≠ 2 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 := congrArg Padic.valuation h
  have h2 : (2 : ℚ_[2]).valuation = 1 := by exact_mod_cast Padic.valuation_p (p := 2)
  rw [Padic.valuation_pow, h2] at h1
  omega⟩

theorem dyadic_ramified : ∃ P : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℚ_[2] 2 0), P.det ≠ 0 ∧
    !![1, 0; 0, 1] = Pᵀ * !![3, 0; 0, 3] * P.map (conjSqrt 2) := by
  haveI := GlobalTheory.SplitWeil.Model.padic_localField 2
  haveI := isQuadratic (2 : ℚ_[2])
  haveI : CharZero (QuadraticAlgebra ℚ_[2] 2 0) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[2] _).injective
  refine (GlobalTheory.Published.hermitianLocalGlobal_holds.1 ℚ_[2] two_ne_zero _ (conjSqrt 2)
    (conjSqrt_ne_one 2 two_ne_zero) 2 _ _ ?_ ?_ ?_ ?_).2 ⟨3, ?_⟩
  · intro a b; fin_cases a <;> fin_cases b <;> simp [map_ofNat]
  · intro a b; fin_cases a <;> fin_cases b <;> simp
  · simp [Matrix.det_fin_two]
  · simp [Matrix.det_fin_two]
  · simp [Matrix.det_fin_two, map_ofNat]

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem norm_one_add_sq (t : ℚ_[3]) (ht : ‖t‖ ≤ 1) : ‖1 + t ^ 2‖ = 1 := by
  let s : ℤ_[3] := ⟨t, ht⟩
  have hu : IsUnit (1 + s ^ 2) := by
    by_contra h
    have h1 : 1 + s ^ 2 ∈ RingHom.ker (PadicInt.toZMod (p := 3)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, map_add, map_pow, map_one] at h1
    revert h1
    generalize PadicInt.toZMod s = z
    revert z; decide
  exact PadicInt.isUnit_iff.1 hu

theorem sum_squares_ne_three_three_adic (x y : ℚ_[3]) (hxy : ‖y‖ ≤ ‖x‖) : x ^ 2 + y ^ 2 ≠ 3 := by
  intro h
  have hx : x ≠ 0 := by
    rintro rfl
    have : y = 0 := by simpa using hxy
    subst this
    norm_num at h
  have ht : ‖y / x‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hxy (norm_nonneg _)
  have h1 := norm_one_add_sq _ ht
  have h0 : 1 + (y / x) ^ 2 ≠ 0 := by intro h0; rw [h0] at h1; simp at h1
  have hv : (1 + (y / x) ^ 2).valuation = 0 := by
    rw [Padic.norm_eq_zpow_neg_valuation h0] at h1
    have := (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 h1
    omega
  have h2 : x ^ 2 * (1 + (y / x) ^ 2) = 3 := by rw [← h]; field_simp
  have h3 := congrArg Padic.valuation h2
  have h4 : (3 : ℚ_[3]).valuation = 1 := by exact_mod_cast Padic.valuation_p (p := 3)
  rw [Padic.valuation_mul (pow_ne_zero _ hx) h0, Padic.valuation_pow, hv, h4] at h3
  omega

theorem three_not_sum (x y : ℚ_[3]) : x ^ 2 + y ^ 2 ≠ 3 := by
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact sum_squares_ne_three_three_adic x y h
  · rw [add_comm]; exact sum_squares_ne_three_three_adic y x h

instance neg_one_not_sq : Fact (∀ r : ℚ_[3], r ^ 2 ≠ -1 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 : ‖r‖ ^ 2 = 1 := by rw [← norm_pow, h]; simp
  have h2 : ‖r‖ ≤ 1 := by nlinarith [norm_nonneg r]
  have := norm_one_add_sq r h2
  rw [h] at this
  simp at this⟩

theorem unramified_two_classes : ¬ ∃ P : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℚ_[3] (-1) 0),
    P.det ≠ 0 ∧ !![1, 0; 0, 1] = Pᵀ * !![1, 0; 0, 3] * P.map (conjSqrt (-1)) := by
  haveI := GlobalTheory.SplitWeil.Model.padic_localField 3
  haveI := isQuadratic (-1 : ℚ_[3])
  haveI : CharZero (QuadraticAlgebra ℚ_[3] (-1) 0) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[3] _).injective
  rw [GlobalTheory.Published.hermitianLocalGlobal_holds.1 ℚ_[3] two_ne_zero _ (conjSqrt (-1))
    (conjSqrt_ne_one (-1) two_ne_zero) 2 _ _ ?_ ?_ ?_ ?_]
  · rintro ⟨x, hx⟩
    have h3 : (3 : QuadraticAlgebra ℚ_[3] (-1) 0) = x * star x := by
      simpa [Matrix.det_fin_two, conjSqrt_apply] using hx
    have := congrArg QuadraticAlgebra.re h3
    have h4 : (3 : QuadraticAlgebra ℚ_[3] (-1) 0).re = 3 := by
      exact_mod_cast QuadraticAlgebra.re_natCast (R := ℚ_[3]) (a := -1) (b := 0) 3
    rw [h4] at this
    simp at this
    exact three_not_sum x.re x.im (by rw [this]; ring)
  · intro a b; fin_cases a <;> fin_cases b <;> simp [map_ofNat]
  · intro a b; fin_cases a <;> fin_cases b <;> simp
  · simp [Matrix.det_fin_two]
  · simp [Matrix.det_fin_two]

section Global
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hyperbolic_hyp :
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      CongrOver (v.adicCompletion (maximalRealSubfield E))
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) !![2, 0; 0, -2]) ∧
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
      (!![2, 0; 0, -2] : Matrix (Fin 2) (Fin 2) E).map τ =
        Qᵀ * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E).map τ * Q.map conj) := by
  have h : ∃ P : Matrix (Fin 2) (Fin 2) E, P.det ≠ 0 ∧
      (!![2, 0; 0, -2] : Matrix (Fin 2) (Fin 2) E) = Pᵀ * !![0, 1; 1, 0] * P.map cc := by
    refine ⟨!![1, 1; 1, -1], by simp [Matrix.det_fin_two]; norm_num, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, cc] <;> norm_num
  exact ⟨fun _ => CongrOver.of_congr h, GlobalTheory.Published.Landherr.congr_complex h⟩

theorem arch_separates (τ : E →+* ℂ) : ¬ ∃ Q : Matrix (Fin 1) (Fin 1) ℂ, Q.det ≠ 0 ∧
    (!![-1] : Matrix (Fin 1) (Fin 1) E).map τ =
      Qᵀ * (!![1] : Matrix (Fin 1) (Fin 1) E).map τ * Q.map conj := by
  rintro ⟨Q, -, h⟩
  have := congrArg Complex.re (congrFun (congrFun h 0) 0)
  simp [Matrix.mul_apply] at this
  nlinarith [mul_self_nonneg (Q 0 0).re, mul_self_nonneg (Q 0 0).im]

end Global

theorem exists_cm : ∃ _ : IsCMField (CyclotomicField 4 ℚ),
    Nonempty (HeightOneSpectrum (𝓞 (maximalRealSubfield (CyclotomicField 4 ℚ)))) := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) := by
    have h : @IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) _ _ (CyclotomicField.algebra 4 ℚ) :=
      inferInstance
    convert h
    exact Subsingleton.elim _ _
  refine ⟨IsCyclotomicExtension.Rat.isCMField _ (S := {4}) ⟨4, rfl, by norm_num⟩, ?_⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 (maximalRealSubfield (CyclotomicField 4 ℚ)))
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)⟩⟩

end GlobalTheory.HermLocal.Model
