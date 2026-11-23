import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.SteinFibre

theorem exists_mul_eq_mul_pow_of_uniformizer {A : Type} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime] (π a : A) (n : ℕ) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2)
    (ha : a ∈ P ^ n) (ha1 : a ∉ P ^ (n + 1)) :
    ∃ s s' : A, s ∉ P ∧ s' ∉ P ∧ s' * a = s * π ^ n := by
  have h1 : P ∣ Ideal.span {π} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hπ)
  obtain ⟨J, hJ⟩ := h1
  have hJP : ¬ J ≤ P := fun h => hπ2 (by
    have : Ideal.span {π} ≤ P ^ 2 := by rw [hJ, sq]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self π))
  have hJn : ¬ J ^ n ≤ P := fun h => hJP (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨s', hs'J, hs'P⟩ := SetLike.not_le_iff_exists.1 hJn
  have hmem : s' * a ∈ Ideal.span {π ^ n} := by
    rw [← Ideal.span_singleton_pow, hJ, mul_pow, mul_comm]
    exact Ideal.mul_mem_mul hs'J ha
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨s, s', ?_, hs'P, hs.symm⟩
  intro hsP
  have h2 : s' * a ∈ P ^ (n + 1) := by
    rw [← hs, pow_succ']
    exact Ideal.mul_mem_mul hsP (Ideal.pow_mem_pow hπ n)
  rcases Ideal.IsPrime.mul_mem_pow P h2 with h | h
  · exact hs'P h
  · exact ha1 h

theorem ord_eq_zero_of_not_mem_under {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (z : X) (a : Γ(X, ⊤)) (ha : a ∉ under z) :
    Scheme.ord (algebraMap Γ(X, ⊤) X.functionField a) z = 0 := by
  have hu : IsUnit (X.presheaf.germ ⊤ z trivial a) := by
    by_contra h
    exact ha ((mem_under_iff z a).2 h)
  have hzV : z ∈ X.basicOpen a := (X.mem_basicOpen a z trivial).2 hu
  haveI : Nonempty (X.basicOpen a) := ⟨⟨z, hzV⟩⟩
  have h1 := Scheme.ord_of_isUnit (U := X.basicOpen a) (f := X.presheaf.map (homOfLE le_top).op a)
    (X.toRingedSpace.isUnit_res_basicOpen a) hzV
  rw [← h1]
  congr 1
  exact (X.presheaf.germ_res_apply (homOfLE le_top) _ _ a).symm

theorem ord_pow_of_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (z : X) (f : X.functionField) (hf : f ≠ 0) (n : ℕ) :
    Scheme.ord (f ^ n) z = n * Scheme.ord f z := by
  induction n with
  | zero =>
    have h := Scheme.ord_mul (x := z) (one_ne_zero (α := X.functionField))
      (one_ne_zero (α := X.functionField))
    simp only [mul_one] at h
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    omega
  | succ k ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

theorem ord_eq_mul_ord_uniformizer : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsDedekindDomain Γ(X, ⊤)] (z : X)
    (P : Ideal Γ(X, ⊤)) (π a : Γ(X, ⊤)) (n : ℕ), P.IsPrime → P ≠ ⊥ → GlobalTheory.SteinFibre.under z = P →
    π ∈ P → π ∉ P ^ 2 → a ∈ P ^ n → a ∉ P ^ (n + 1) →
      Scheme.ord (algebraMap Γ(X, ⊤) X.functionField a) z =
        n * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField π) z := by
  intro X _ _ _ z P π a n hP _ hz hπ hπ2 ha ha1
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  have inj : Function.Injective (algebraMap Γ(X, ⊤) X.functionField) :=
    X.germToFunctionField_injective ⊤
  obtain ⟨s, s', hs, hs', he⟩ := exists_mul_eq_mul_pow_of_uniformizer P π a n hπ hπ2 ha ha1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha1 (Ideal.zero_mem _)
  have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (Ideal.zero_mem _)
  have hs0 : s ≠ 0 := by rintro rfl; exact hs (Ideal.zero_mem _)
  have hs'0 : s' ≠ 0 := by rintro rfl; exact hs' (Ideal.zero_mem _)
  rw [← hz] at hs hs'
  have nz : ∀ x : Γ(X, ⊤), x ≠ 0 → algebraMap Γ(X, ⊤) X.functionField x ≠ 0 :=
    fun x hx => (map_ne_zero_iff _ inj).2 hx
  have key := congrArg (fun x => Scheme.ord (algebraMap Γ(X, ⊤) X.functionField x) z) he
  simp only [map_mul, map_pow] at key
  rw [Scheme.ord_mul (nz s' hs'0) (nz a ha0), Scheme.ord_mul (nz s hs0) (pow_ne_zero _ (nz π hπ0)),
    ord_eq_zero_of_not_mem_under z s' hs', ord_eq_zero_of_not_mem_under z s hs, zero_add, zero_add,
    ord_pow_of_ne_zero z _ (nz π hπ0)] at key
  exact key

end GlobalTheory.SteinFibre
