import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.Published.LandherrModel

abbrev Qi : Type := CyclotomicField 4 ℚ

instance cyclo : IsCyclotomicExtension {4} ℚ Qi := by
  have h : @IsCyclotomicExtension {4} ℚ Qi _ _ (CyclotomicField.algebra 4 ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

instance cm : IsCMField Qi := IsCyclotomicExtension.Rat.isCMField Qi (S := {4}) ⟨4, rfl, by norm_num⟩

noncomputable def ii : Qi := IsCyclotomicExtension.zeta 4 ℚ Qi

theorem ii_mul : ii * ii = -1 := by
  have h := IsCyclotomicExtension.zeta_spec 4 ℚ Qi
  have := (h.pow (a := 2) (b := 2) (by norm_num) (by norm_num)).eq_neg_one_of_two_right
  rw [← this, pow_two]; rfl

theorem cc_ii : IsCMField.complexConj Qi ii = -ii := by
  let τ : Qi →+* ℂ := Classical.choice inferInstance
  apply τ.injective
  have h : τ ii * τ ii = -1 := by rw [← map_mul, ii_mul]; simp
  have h' : τ ii = Complex.I ∨ τ ii = -Complex.I := by
    rw [← mul_self_eq_mul_self_iff, h]; simp
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  rcases h' with h' | h' <;> simp [h']

noncomputable def A : Matrix (Fin 2) (Fin 2) Qi := !![1, ii; -ii, 3]

theorem A_herm (a b : Fin 2) : cc (A a b) = A b a := by
  have h3 : IsCMField.complexConj Qi 3 = 3 := map_ofNat _ 3
  fin_cases a <;> fin_cases b <;> simp [A, cc, cc_ii, h3]

theorem A_det : A.det = 2 := by
  simp only [A, Matrix.det_fin_two_of]
  linear_combination ii_mul

theorem A_congr : ∃ P : Matrix (Fin 2) (Fin 2) Qi, P.det ≠ 0 ∧ A = Pᵀ * 1 * P.map cc := by
  have hne : (1 : Qi) + ii ≠ 0 := by
    intro h
    have : (2 : Qi) = 0 := by linear_combination (1 - ii) * h + ii_mul
    norm_num at this
  refine ⟨!![1, -ii; 0, 1 + ii], by simpa [Matrix.det_fin_two] using hne, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two, cc, cc_ii]
  linear_combination 2 * ii_mul

theorem hypotheses :
    (∀ a b, cc ((1 : Matrix (Fin 2) (Fin 2) Qi) a b) = (1 : Matrix (Fin 2) (Fin 2) Qi) b a) ∧
    (∀ a b, cc (A a b) = A b a) ∧ (1 : Matrix (Fin 2) (Fin 2) Qi).det ≠ 0 ∧ A.det ≠ 0 ∧
    (∀ τ : Qi →+* ℂ, ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
      A.map τ = Qᵀ * (1 : Matrix (Fin 2) (Fin 2) Qi).map τ * Q.map conj) ∧
    ∃ x : Qi, (1 : Matrix (Fin 2) (Fin 2) Qi).det / A.det = x * cc x := by
  refine ⟨?_, A_herm, by simp, by rw [A_det]; norm_num, Landherr.congr_complex A_congr,
    Landherr.det_norm (by simp) A_congr⟩
  intro a b
  fin_cases a <;> fin_cases b <;> simp [cc]

theorem three_ne_sq_add_sq (a b : ℚ) : (3 : ℚ) ≠ a ^ 2 + b ^ 2 := by
  intro h
  set D : ℕ := a.den * b.den with hD
  have hD0 : D ≠ 0 := mul_ne_zero a.den_nz b.den_nz
  have key : 3 * D ^ 2 = (a.num * b.den).natAbs ^ 2 + (b.num * a.den).natAbs ^ 2 := by
    have : (3 * (D : ℤ) ^ 2) = (a.num * b.den) ^ 2 + (b.num * a.den) ^ 2 := by
      have ha : (a.num : ℚ) = a * a.den := (Rat.mul_den_eq_num a).symm
      have hb : (b.num : ℚ) = b * b.den := (Rat.mul_den_eq_num b).symm
      have : ((3 * (D : ℤ) ^ 2 : ℤ) : ℚ) = (((a.num * b.den) ^ 2 + (b.num * a.den) ^ 2 : ℤ) : ℚ) := by
        push_cast [hD]
        rw [ha, hb]
        linear_combination ((a.den : ℚ) * b.den) ^ 2 * h
      exact_mod_cast this
    zify
    rw [sq_abs, sq_abs]
    exact this
  have h2 := (Nat.eq_sq_add_sq_iff (n := 3 * D ^ 2)).mp ⟨_, _, key⟩ 3
    (by
      rw [Nat.mem_primeFactors]
      exact ⟨by norm_num, dvd_mul_right _ _, by positivity⟩) (by norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [padicValNat.mul (by norm_num) (pow_ne_zero _ hD0), padicValNat.pow,
    padicValNat_self] at h2
  rw [Nat.even_add] at h2
  simp at h2

theorem exists_coord (x : Qi) : ∃ a b : ℚ, x = a + b * ii := by
  have hli : LinearIndependent ℚ ![(1 : Qi), ii] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : Qi) + (t : Qi) * ii = 0 := by
      simpa [Algebra.smul_def] using hst
    have h2 : ((s ^ 2 + t ^ 2 : ℚ) : Qi) = 0 := by
      push_cast
      linear_combination ((s : Qi) - t * ii) * h1 + (t : Qi) ^ 2 * ii_mul
    have h3 : s ^ 2 + t ^ 2 = 0 := by exact_mod_cast h2
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg t]
  have hr : Module.finrank ℚ Qi = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 4) Qi
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hr]; simp)
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  conv_lhs => rw [← b.sum_repr x, Fin.sum_univ_two]
  simp [b, Algebra.smul_def]

theorem three_not_norm : ¬ ∃ x : Qi, (3 : Qi) = x * cc x := by
  rintro ⟨x, hx⟩
  obtain ⟨a, b, rfl⟩ := exists_coord x
  apply three_ne_sq_add_sq a b
  simp only [cc, map_add, map_mul, map_ratCast, cc_ii] at hx
  have : ((3 : ℚ) : Qi) = ((a ^ 2 + b ^ 2 : ℚ) : Qi) := by
    push_cast
    linear_combination hx - (b : Qi) ^ 2 * ii_mul
  exact_mod_cast this

theorem det_needed :
    (∀ τ : Qi →+* ℂ, ∃ Q : Matrix (Fin 1) (Fin 1) ℂ, Q.det ≠ 0 ∧
      (!![3] : Matrix (Fin 1) (Fin 1) Qi).map τ =
        Qᵀ * (!![1] : Matrix (Fin 1) (Fin 1) Qi).map τ * Q.map conj) ∧
    ¬ ∃ P : Matrix (Fin 1) (Fin 1) Qi, P.det ≠ 0 ∧
      (!![3] : Matrix (Fin 1) (Fin 1) Qi) = Pᵀ * !![1] * P.map cc := by
  constructor
  · intro τ
    refine ⟨!![((Real.sqrt 3 : ℝ) : ℂ)], by simp, ?_⟩
    ext a b
    fin_cases a; fin_cases b
    have h3 : τ 3 = 3 := map_ofNat _ 3
    simp [Matrix.mul_apply, h3, ← Complex.ofReal_mul]
  · rintro ⟨P, -, h⟩
    refine three_not_norm ⟨P 0 0, ?_⟩
    simpa [Matrix.mul_apply] using congrFun (congrFun h 0) 0

theorem signature_needed :
    (∃ x : Qi, (1 : Matrix (Fin 2) (Fin 2) Qi).det / (-1 : Matrix (Fin 2) (Fin 2) Qi).det = x * cc x) ∧
    ¬ ∃ P : Matrix (Fin 2) (Fin 2) Qi, P.det ≠ 0 ∧
      (-1 : Matrix (Fin 2) (Fin 2) Qi) = Pᵀ * 1 * P.map cc := by
  refine ⟨⟨1, by simp [cc, Matrix.det_neg]⟩, fun h => ?_⟩
  obtain ⟨Q, -, h⟩ := Landherr.congr_complex h (Classical.choice inferInstance)
  have h0 := congrArg Complex.re (congrFun (congrFun h 0) 0)
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h0
  nlinarith [mul_self_nonneg (Q 0 0).re, mul_self_nonneg (Q 0 0).im, mul_self_nonneg (Q 1 0).re,
    mul_self_nonneg (Q 1 0).im]

theorem hasseNorm_iff (H : HasseNorm) (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (a : K) (ha : a ≠ 0) :
    ((∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L,
      Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) a) ∧
    (∀ v : InfinitePlace K, ∃ z : v.Completion ⊗[K] L,
      Algebra.norm v.Completion z = algebraMap K v.Completion a)) ↔
    ∃ x : L, Algebra.norm K x = a :=
  ⟨fun h => H K L a ha h.1 h.2,
    fun h => ⟨fun _ => HasseNorm.local_of_global _ h, fun _ => HasseNorm.local_of_global _ h⟩⟩

end GlobalTheory.Published.LandherrModel
