import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial TrivSqZeroExt

noncomputable section
namespace GlobalTheory.K5.DlogUniq

section generic
variable {R : Type*} [CommRing R]

theorem aeval_dual {S : Type*} [CommRing S] [Algebra R S] (a m : S) (f : R[X]) :
    (aeval (inl a + inr m : DualNumber S) f).fst = aeval a f ∧
    (aeval (inl a + inr m : DualNumber S) f).snd = aeval a (derivative f) * m := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, fst_add, snd_add, hf.1, hf.2, hg.1, hg.2, map_add, map_add, map_add, add_mul]
    exact ⟨rfl, rfl⟩
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, derivative_monomial, aeval_monomial]
    constructor
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_pow]
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_pow]
      ring

theorem exists_derivation (Φ : R[X]) (N : ℕ) (q : R) (I : Ideal R[X][X])
    (hI : I = Ideal.span {C Φ, X ^ N - C (C q)}) (S : Type*) [CommRing S] [Algebra R S]
    [Algebra (R[X][X] ⧸ I) S] [IsScalarTower R (R[X][X] ⧸ I) S] (mx my : S)
    (hx : algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) (derivative Φ)) * mx = 0)
    (hy : (N : S) * my = 0) :
    ∃ D : Derivation R (R[X][X] ⧸ I) S,
      D (Ideal.Quotient.mk I (C X)) = mx ∧ D (Ideal.Quotient.mk I X) = my := by
  let π : R[X][X] →+* S := (algebraMap (R[X][X] ⧸ I) S).comp (Ideal.Quotient.mk I)
  let ψ0 : R[X][X] →+* DualNumber S :=
    eval₂RingHom (aeval (inl (π (C X)) + inr mx : DualNumber S) : R[X] →ₐ[R] DualNumber S).toRingHom
      (inl (π X) + inr my)
  have hC : ∀ f : R[X], ψ0 (C f) = aeval (inl (π (C X)) + inr mx : DualNumber S) f := by
    intro f; simp [ψ0]
  have hX : ψ0 X = inl (π X) + inr my := by simp [ψ0]
  have hπC : ∀ f : R[X], aeval (π (C X)) f = π (C f) := by
    intro f
    have : (aeval (π (C X)) : R[X] →ₐ[R] S).toRingHom = π.comp C := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
        exact IsScalarTower.algebraMap_apply R (R[X][X] ⧸ I) S a
      · simp
    exact congrArg (fun g => g f) this
  have hπC' : ∀ f : R[X], aeval (π (C X)) f =
      algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) f) := by
    intro f
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R (R[X][X] ⧸ I) S) (Ideal.Quotient.mk I (C X)) f)
  have hfst : ∀ f, (ψ0 f).fst = π f := by
    intro f
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp ψ0 = π := by
      apply Polynomial.ringHom_ext
      · intro a
        show (ψ0 (C a)).fst = _
        rw [hC, (aeval_dual _ _ _).1, hπC]
      · show (ψ0 X).fst = _
        rw [hX]; simp
    exact congrArg (fun g => g f) this
  have hπI : ∀ f ∈ I, π f = 0 := by
    intro f hf
    show algebraMap (R[X][X] ⧸ I) S (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have hker : ∀ f ∈ I, ψ0 f = 0 := by
    have : I ≤ RingHom.ker ψ0 := by
      have h1 : C Φ ∈ I := hI ▸ Ideal.subset_span (by simp)
      have h2 : X ^ N - C (C q) ∈ I := hI ▸ Ideal.subset_span (by simp)
      refine hI.le.trans (Ideal.span_le.2 ?_)
      rintro f (rfl | rfl)
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h1]; rfl
        · rw [hC, (aeval_dual _ _ _).2, hπC']; exact hx
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h2]; rfl
        · rw [map_sub, map_pow, hX, hC, aeval_C, snd_sub, snd_pow, TrivSqZeroExt.algebraMap_eq_inl']
          simp only [snd_add, snd_inl, snd_inr, zero_add, sub_zero, snd_zero, smul_eq_mul, nsmul_eq_mul]
          rw [mul_left_comm, hy, mul_zero]
    exact fun f hf => this hf
  let ψ : (R[X][X] ⧸ I) →+* DualNumber S := Ideal.Quotient.lift I ψ0 hker
  have hψ : ∀ z, (ψ z).fst = algebraMap (R[X][X] ⧸ I) S z := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hfst f
  have hleib : ∀ a b, (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd := by
    intro a b
    rw [map_mul, DualNumber.snd_mul, hψ, hψ, Algebra.smul_def, Algebra.smul_def, mul_comm (ψ a).snd]
  have halg : ∀ c : R, (ψ (algebraMap R _ c)).snd = 0 := by
    intro c
    show (ψ0 (C (C c))).snd = 0
    rw [hC, (aeval_dual _ _ _).2]; simp
  let L : (R[X][X] ⧸ I) →ₗ[R] S :=
    { toFun := fun z => (ψ z).snd
      map_add' := fun a b => by rw [map_add, snd_add]
      map_smul' := fun c z => by
        rw [Algebra.smul_def, hleib, halg, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' L hleib, ?_, ?_⟩
  · show (ψ0 (C X)).snd = mx
    rw [hC]; simp
  · show (ψ0 X).snd = my
    rw [hX]; simp

end generic

variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_quot {A : Type*} [CommRing A] (k l : ℕ) :
    ((k ^ l : ℕ) : A ⧸ Ideal.span {(k : A) ^ l}) * 1 = 0 := by
  rw [mul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(k : A) ^ l})),
    Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

theorem aeval_xn (n : ℕ) (f : (O0 p)[X]) :
    aeval (xn p n) f = Ideal.Quotient.mk (towerIdeal p n) (C f) := by
  have : (aeval (xn p n) : (O0 p)[X] →ₐ[O0 p] On p n).toRingHom =
      (Ideal.Quotient.mk (towerIdeal p n)).comp C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
      rfl
    · simp [xn]
  exact congrArg (fun g => g f) this

theorem aeval_xn_cyclotomic (n : ℕ) : aeval (xn p n) (cyclotomic (p ^ n) (O0 p)) = 0 := by
  rw [aeval_xn, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

theorem isUnit_xn (m : ℕ) : IsUnit (xn p (m + 1)) := by
  have h := congrArg (aeval (xn p (m + 1))) (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  rw [map_mul, aeval_xn_cyclotomic, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact IsUnit.of_pow_eq_one (sub_eq_zero.1 h.symm) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

theorem isUnit_yn (n : ℕ) : IsUnit (yn p n) := by
  have hq : IsUnit (qO p) := by
    refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
    rw [HahnSeries.single_mul_single]; simp
  have h : yn p n ^ (p ^ n) = Ideal.Quotient.mk (towerIdeal p n) (C (C (qO p))) := by
    rw [yn, ← map_pow, Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)
  have h2 : IsUnit (yn p n ^ (p ^ n)) := h ▸ ((hq.map _).map _).map _
  exact (isUnit_pow_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).1 h2

theorem derivative_cyclotomic_mul (m : ℕ) :
    aeval (xn p (m + 1)) (derivative (cyclotomic (p ^ (m + 1)) (O0 p))) * (xn p (m + 1) ^ p ^ m - 1) =
      (p : On p (m + 1)) ^ (m + 1) * xn p (m + 1) ^ (p ^ (m + 1) - 1) := by
  have h := congrArg (fun f => aeval (xn p (m + 1)) (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, map_add, map_mul, aeval_xn_cyclotomic, zero_mul, add_zero] at h
  simpa [derivative_X_pow] using h

end GlobalTheory.K5.DlogUniq
