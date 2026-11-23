import Mathlib

namespace GlobalTheory.NormExtensionBound

open scoped Pointwise

theorem exists_extension {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    (ev : A →+* K) : ∃ ev' : B →+* K, ∀ a, ev' (algebraMap A B a) = ev a := by
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker ev) ⊥ (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ (B ⧸ Q) (by rw [h, map_zero])
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) K :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ K (by rw [h, map_zero])
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let f : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker ev] K := IsAlgClosed.lift
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun a => ?_⟩
  have h := f.commutes (Ideal.Quotient.mk _ a)
  exact h

theorem norm_le_one_of_extension {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (ev : A →+* PadicAlgCl p) (h : ∀ a, ‖ev a‖ ≤ 1)
    (ev' : B →+* PadicAlgCl p) (hev : ∀ a, ev' (algebraMap A B a) = ev a) (b : B) :
    ‖ev' b‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  have hcomp : ev'.comp (algebraMap A B) = ev := RingHom.ext hev
  have hq' := congrArg ev' hq
  rw [map_zero, Polynomial.hom_eval₂, hcomp, hqm.as_sum, Polynomial.eval₂_add,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hq'
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq'
  set y := ev' b
  by_contra hy
  push_neg at hy
  have hxn : y ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i :=
    eq_neg_of_add_eq_zero_left hq'
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hy1 : 1 ≤ ‖y‖ := hy.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, ev (q.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖ev (q.coeff i)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (q.natDegree - 1) :=
          mul_le_mul (h _) (pow_le_pow_right₀ hy1 (by omega)) (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖y‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖y‖ ^ q.natDegree ≤ ‖y‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖y‖ ^ (q.natDegree - 1) < ‖y‖ ^ q.natDegree := pow_lt_pow_right₀ hy (by omega)
  linarith

theorem main : ∀ (p : ℕ) [Fact (Nat.Prime p)] (A B : Type) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)]
    (𝔷 : Ideal B), Function.Injective (algebraMap A B) →
    (∀ (b : B), (∀ (σ : B ≃ₐ[A] B), σ b = b) → b ∈ Set.range (algebraMap A B)) →
    Ideal.IsMaximal 𝔷 → ∀ (ev : A →+* PadicAlgCl p), (∀ (a : A), ‖ev a‖ ≤ (1 : ℝ)) →
    (∀ a ∈ IsLocalRing.maximalIdeal A, ‖ev a‖ < (1 : ℝ)) →
    ∃ (ev' : B →+* PadicAlgCl p), (∀ (a : A), ev' (algebraMap A B a) = ev a) ∧
      (∀ (b : B), ‖ev' b‖ ≤ (1 : ℝ)) ∧ ∀ b ∈ 𝔷, ‖ev' b‖ < (1 : ℝ) := by
  intro p _ A B _ _ _ _ _ _ _ 𝔷 hinj hfix hmax ev h1 h2
  obtain ⟨e, he⟩ := exists_extension hinj ev
  have hle := norm_le_one_of_extension ev h1 e he
  let m : Ideal B :=
    { carrier := {b | ‖e b‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖e (a + b)‖ < 1
        rw [map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        show ‖e (c * b)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hb }
  have hm : ∀ b, b ∈ m ↔ ‖e b‖ < 1 := fun _ => Iff.rfl
  have hmne : m ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hm]
    simp
  have hmu : m.under A = IsLocalRing.maximalIdeal A := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hmne)
    intro a ha
    rw [Ideal.mem_comap, hm, he]
    exact h2 a ha
  haveI hmm : m.IsPrime := ⟨hmne, fun {a b} hab => by
    rw [hm, map_mul, norm_mul] at hab
    by_contra hc
    rw [not_or, hm, hm, not_lt, not_lt] at hc
    exact absurd hab (not_lt.2 (one_le_mul_of_one_le_of_one_le hc.1 hc.2))⟩
  have hzu : 𝔷.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) 𝔷)
  haveI : Algebra.IsInvariant A B (B ≃ₐ[A] B) := ⟨fun b hb => hfix b hb⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B (B ≃ₐ[A] B) 𝔷 m
    (hzu.trans hmu.symm)
  refine ⟨e.comp (g : B →+* B), fun a => ?_, fun b => hle _, fun b hb => ?_⟩
  · simp [he]
  · have : g • b ∈ m := by
      rw [hg]
      exact Ideal.smul_mem_pointwise_smul g b 𝔷 hb
    exact this

end GlobalTheory.NormExtensionBound
