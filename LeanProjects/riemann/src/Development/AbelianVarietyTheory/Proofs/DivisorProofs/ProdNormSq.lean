import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TermUnit

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

omit [NumberField E] [Fintype I] in

theorem bijective_mk {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  constructor
  · intro i j hij
    have hj := InfinitePlace.mk_eq_iff.mp hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have e1 : i = k := hk i (hj.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))
    have e2 : j = k := hk j (Or.inl rfl)
    rw [e1, e2]
  · intro w
    obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    show InfinitePlace.mk (φ i) = w
    rcases hi with hi | hi
    · rw [← hi, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq (φ i), ← hi, InfinitePlace.mk_embedding]

theorem prod_norm_sq [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |(Algebra.norm ℚ x : ℝ)| := by
  calc ∏ i, ‖φ i x‖ ^ 2 = ∏ w : InfinitePlace E, w x ^ InfinitePlace.mult w :=
        Fintype.prod_bijective _ (bijective_mk h) _ _ fun i => by
          rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]
    _ = _ := by rw [InfinitePlace.prod_eq_abs_norm]; push_cast; rfl

theorem prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (z : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ z = ((∏ j ∈ t, f j : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem term_unit [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (u : (OF E)ˣ) :
    term φ (2 * s) κ σ (algebraMap (OF E) E u) = 1 := by
  set x := algebraMap (OF E) E (u : OF E) with hxdef
  have hxmem : x ∈ maximalRealSubfield E := by
    rw [hxdef, IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
    exact (algebraMap (OF E) (maximalRealSubfield E) u).2
  have hreal : ∀ i, starRingEnd ℂ (φ i x) = φ i x := fun i => by
    rw [starRingEnd_apply]
    exact (mem_maximalRealSubfield_iff x).mp hxmem (φ i)
  have hx0 : x ≠ 0 := (u.isUnit.map (algebraMap (OF E) E)).ne_zero
  have hN : |(Algebra.norm ℚ x : ℝ)| = 1 := by
    have hv := NumberField.isUnit_iff_norm.mp (u.isUnit.map (algebraMap (OF E) (𝓞 E)))
    have hc : ((algebraMap (OF E) (𝓞 E) u : 𝓞 E) : E) = x :=
      (IsScalarTower.algebraMap_apply (OF E) (𝓞 E) E u).symm
    rw [RingOfIntegers.coe_norm, hc] at hv
    exact_mod_cast hv
  have hprod : ∏ i, ‖φ i x‖ = 1 := by
    have hsq : (∏ i, ‖φ i x‖) ^ 2 = 1 := by rw [← Finset.prod_pow, prod_norm_sq h x, hN]
    exact (pow_eq_one_iff_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) two_ne_zero).mp hsq
  have hfac : ∀ i, (φ i x)⁻¹ ^ (2 * s + κ i) * starRingEnd ℂ (φ i x) ^ κ i * ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * ((s : ℂ) + σ)) := fun i => by
    have hr : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx0
    have ha : ((‖φ i x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
    have hsq : ((‖φ i x‖ : ℝ) : ℂ) ^ 2 = φ i x ^ 2 := by
      have hm := Complex.mul_conj (φ i x)
      rw [hreal, Complex.normSq_eq_norm_sq] at hm
      rw [sq (φ i x), hm]
      push_cast
      ring
    rw [show -2 * ((s : ℂ) + σ) = -((2 * s : ℕ) : ℂ) + -2 * σ by push_cast; ring,
      Complex.cpow_add _ _ ha, Complex.cpow_neg, Complex.cpow_natCast, hreal]
    congr 1
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hr, one_pow, mul_one, inv_pow, pow_mul, pow_mul, hsq]
  simp only [term]
  rw [Finset.prod_congr rfl fun i _ => hfac i, prod_cpow _ _ (fun i => norm_nonneg _), hprod]
  simp

theorem norm_term [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) {x : E} (hx : x ≠ 0) :
    ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re)) := by
  have hpos : ∀ i, 0 < ‖φ i x‖ := fun i => norm_pos_iff.mpr ((map_ne_zero (φ i)).mpr hx)
  rw [← prod_norm_sq h x, ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  simp only [term, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha := hpos i
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos ha, inv_pow, ← Real.rpow_natCast _ (2 * s + κ i),
    ← Real.rpow_natCast _ (κ i), ← Real.rpow_neg ha.le, ← Real.rpow_add ha, ← Real.rpow_add ha,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le]
  congr 1
  simp
  ring

private theorem term_mul' (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (σ : ℂ) (y x : E) :
    term φ k κ σ (y * x) = term φ k κ σ y * term φ k κ σ x := by
  simp only [term, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_mul, mul_inv, norm_mul, mul_pow]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

theorem term_unit_and_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (x : E) :
    (∀ u : (OF E)ˣ, term φ (2 * s) κ σ (algebraMap (OF E) E u * x) = term φ (2 * s) κ σ x) ∧
      (x ≠ 0 → ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re))) := by
  refine ⟨fun u => ?_, fun hx => norm_term h s κ σ hx⟩
  rw [term_mul', term_unit h s κ σ u, one_mul]

end GlobalTheory.CMVal.TermUnit
