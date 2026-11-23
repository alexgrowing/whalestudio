import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAdicCompletionSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem hartRep_one (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (a : A) (r : R)
    (h : ∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t}) :
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have hmem : ρ r ∈ Ideal.span {a} := by
    refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one a (ρ r) fun p hp hp1 => ?_
    obtain ⟨u, hu, m', hm⟩ := h p hp hp1
    refine ⟨u, hu, Ideal.mem_span_singleton.2 ⟨ρ m', ?_⟩⟩
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, hρa, hρa, sub_eq_zero] at hm
    exact hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hmem
  refine ⟨algebraMap A R b, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, map_mul, hρa, hρa, hb, sub_self]

theorem hartRep (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (a : A) (ha : a ≠ 0) :
    ∀ n : ℕ, ∀ r : R, (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t ^ n}) →
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t ^ n} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have ht0 : ρ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  intro n
  induction n with
  | zero => intro r _; exact ⟨0, by simp⟩
  | succ n ih =>
    intro r hr
    obtain ⟨x, hx⟩ := hartRep_one A R ρ hρ t hker a r fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      exact ⟨u, hu, m', Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t n.succ_ne_zero) hm⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
    obtain ⟨y', hy'⟩ := ih y fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
      have key : t * (algebraMap A R u * y) - algebraMap A R a * (m' - algebraMap A R u * x)
          = t ^ (n + 1) * q := by
        linear_combination hq - (algebraMap A R u) * hy
      have h2 : a * ρ (m' - algebraMap A R u * x) = 0 := by
        have := congrArg ρ key
        rw [map_sub] at this
        simp only [map_mul, map_pow, ht0, hρa, zero_mul, zero_sub, zero_pow n.succ_ne_zero,
          neg_eq_zero] at this
        exact this
      have h3 : m' - algebraMap A R u * x ∈ Ideal.span {t} := by
        rw [← hker, RingHom.mem_ker]
        exact (mul_eq_zero.1 h2).resolve_left ha
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h3
      refine ⟨u, hu, z, Ideal.mem_span_singleton.2 ⟨q, ?_⟩⟩
      have h4 : t * (algebraMap A R u * y - algebraMap A R a * z - t ^ n * q) = 0 := by
        rw [hz] at key
        linear_combination key
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h4)
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 hy'
    refine ⟨x + t * y', Ideal.mem_span_singleton.2 ⟨s, ?_⟩⟩
    linear_combination hy + t * hs

theorem hart_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.Hart A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', hr'⟩ := hartRep A R ρ hρ t hker ht a ha n r fun p hp hp1 => by
    obtain ⟨u, hu, m', hm'⟩ := hm p hp hp1
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m'
    refine ⟨u, hu, s, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq, Ideal.span_singleton_pow] at hm'
    exact hm'
  refine ⟨Ideal.Quotient.mk _ r', ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow]
  exact hr'

end GlobalTheory.GoodEtaleSection
