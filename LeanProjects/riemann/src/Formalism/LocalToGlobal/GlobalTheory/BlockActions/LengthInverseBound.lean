import Formalism.SatakeDualWeyl.Statement
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.InvariantKernelTraceVanishes

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG

section Sesq

variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)

theorem hform_add_left (x x' y : Fin n → E) : hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (x y y' : Fin n → E) : hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (r : E) (x y : Fin n → E) : hform σ J (r • x) y = σ r * hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_right (r : E) (x y : Fin n → E) : hform σ J x (r • y) = r * hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Sesq

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem length_inverse_bound (σ : E →+* E) (hσ : ∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x))
    (J : Matrix (Fin n) (Fin n) E)
    (hdef : ∀ (φ : E →+* ℂ) (x : Fin n → E), ∃ r : ℝ, 0 ≤ r ∧ φ (hform σ J x x) = r ∧ (r = 0 → x = 0))
    (L : Submodule (𝓞 E) (Fin n → E)) (hint : ∀ x ∈ L, ∃ a : 𝓞 E, (a : E) = hform σ J x x)
    (z : Fin n → E) (hzL : ∀ x ∈ L, hform σ J x z = 0 ∧ hform σ J z x = 0)
    (T : ℕ) (hT : 1 < T) (hz : (T : E) * hform σ J z z = 1)
    (y : Fin n → E) (hy : y ∈ L ⊔ Submodule.span (𝓞 E) {z}) (hyy : (T : E) * hform σ J y y = 1) :
    ∃ b : 𝓞 E, (∃ k : ℕ, 0 < k ∧ b ^ k = 1) ∧ y = (b : E) • z := by
  obtain ⟨x, hxL, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have haz : (a • z : Fin n → E) = algebraMap (𝓞 E) E a • z := (algebraMap_smul E a z).symm
  rw [haz] at hyy ⊢
  have hxz := hzL x hxL
  have hexp : hform σ J (x + algebraMap (𝓞 E) E a • z) (x + algebraMap (𝓞 E) E a • z) =
      hform σ J x x + σ (algebraMap (𝓞 E) E a) * algebraMap (𝓞 E) E a * hform σ J z z := by
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right, hxz.1, hxz.2]
    ring
  have key : (T : E) * hform σ J x x + σ (algebraMap (𝓞 E) E a) * algebraMap (𝓞 E) E a = 1 := by
    rw [hexp] at hyy
    linear_combination hyy - σ (algebraMap (𝓞 E) E a) * algebraMap (𝓞 E) E a * hz
  obtain ⟨c0, hc0⟩ := hint x hxL
  have hT1 : (1 : ℝ) < T := by exact_mod_cast hT
  have hemb : ∀ φ : E →+* ℂ, ‖φ (c0 : E)‖ < 1 ∧ ‖φ (algebraMap (𝓞 E) E a)‖ ≤ 1 ∧
      (‖φ (c0 : E)‖ = 0 → ‖φ (algebraMap (𝓞 E) E a)‖ = 1) := by
    intro φ
    obtain ⟨r, hr0, hr, -⟩ := hdef φ x
    have hk := congrArg φ key
    rw [map_add, map_mul, map_mul, hσ, map_natCast, map_one, hr, Complex.conj_mul'] at hk
    have hk' : (T : ℝ) * r + ‖φ (algebraMap (𝓞 E) E a)‖ ^ 2 = 1 := by exact_mod_cast hk
    have hc : ‖φ (c0 : E)‖ = r := by
      rw [hc0, hr, Complex.norm_real, Real.norm_of_nonneg hr0]
    have hn0 := norm_nonneg (φ (algebraMap (𝓞 E) E a))
    have hTr : 0 ≤ (T : ℝ) * r := mul_nonneg (by linarith) hr0
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      nlinarith [sq_nonneg ‖φ (algebraMap (𝓞 E) E a)‖]
    · nlinarith
    · intro h0
      rw [hc] at h0
      rw [h0, mul_zero, zero_add] at hk'
      exact (pow_eq_one_iff_of_nonneg hn0 two_ne_zero).1 hk'
  have hne : Nonempty (E →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card E ℂ]
    exact Module.finrank_pos
  obtain ⟨φ0⟩ := hne
  have hc0z : (c0 : E) = 0 := by
    by_contra hc
    obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hc
      c0.isIntegral_coe (fun φ => (hemb φ).1.le)
    have h1 := congrArg (fun t => ‖φ0 t‖) hpow
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    have h2 : ‖φ0 (c0 : E)‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg _) (hemb φ0).1 hm.ne'
    linarith
  have hx0 : x = 0 := by
    obtain ⟨r, hr0, hr, hr0'⟩ := hdef φ0 x
    apply hr0'
    rw [← hc0, hc0z, map_zero] at hr
    exact_mod_cast hr.symm
  obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ
    (x := algebraMap (𝓞 E) E a) (by exact a.isIntegral_coe)
    (fun φ => (hemb φ).2.2 (by rw [hc0z, map_zero, norm_zero]))
  refine ⟨a, ⟨m, hm, ?_⟩, ?_⟩
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_pow, hpow, map_one]
  · rw [hx0, zero_add]

theorem root_eq_one (P : Ideal (𝓞 E)) (T k : ℕ) (b : 𝓞 E) (hT : T.Prime) (hP : P.IsPrime)
    (hTP : (T : 𝓞 E) ∈ P) (hk : 0 < k) (hb : b ^ k = 1) (hb1 : b - 1 ∈ P) (hdeg : Module.finrank ℚ E < T - 1) : b = 1 := by
  by_contra hne
  have hfin : IsOfFinOrder b := isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, hb⟩
  have hd1 : orderOf b ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.1 h1)
  obtain ⟨q, hq, e, he⟩ := Nat.exists_prime_and_dvd hd1
  have hη : IsPrimitiveRoot (b ^ e) q :=
    (IsPrimitiveRoot.orderOf b).pow hfin.orderOf_pos (by rw [he, mul_comm])
  have hbP : Ideal.Quotient.mk P b = 1 := by
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact hb1
  have hqP : (q : 𝓞 E) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h0 := congrArg (Ideal.Quotient.mk P) (hη.geom_sum_eq_zero hq.one_lt)
    simpa [map_sum, map_pow, hbP] using h0
  have hTq : T = q := by
    by_contra hne'
    have hcop : Nat.Coprime T q := (Nat.coprime_primes hT hq).2 hne'
    have key : ((Nat.gcd T q : ℤ) : 𝓞 E) =
        (T : 𝓞 E) * (Nat.gcdA T q : 𝓞 E) + (q : 𝓞 E) * (Nat.gcdB T q : 𝓞 E) := by
      rw [Nat.gcd_eq_gcd_ab]
      push_cast
      ring
    rw [hcop.gcd_eq_one] at key
    have h1 : (1 : 𝓞 E) ∈ P := by
      have h := P.add_mem (P.mul_mem_right (Nat.gcdA T q : 𝓞 E) hTP)
        (P.mul_mem_right (Nat.gcdB T q : 𝓞 E) hqP)
      rw [← key] at h
      simpa using h
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  have hηE : IsPrimitiveRoot (algebraMap (𝓞 E) E (b ^ e)) T := by
    rw [hTq]
    exact hη.map_of_injective (IsFractionRing.injective (𝓞 E) E)
  have hdg := minpoly.natDegree_le (A := ℚ) (algebraMap (𝓞 E) E (b ^ e))
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηE hT.pos, Polynomial.natDegree_cyclotomic,
    Nat.totient_prime hT] at hdg
  omega

end Formalism.L2.GlobalTheoryTheory.Br
