import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TraceNondeg

theorem isNilpotent_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (w : A) (h : ∀ y : A, Algebra.trace F A (w * y) = 0) : IsNilpotent w := by
  classical
  let b := Module.finBasis F A
  have hn : IsNilpotent (Algebra.leftMulMatrix b w) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ']
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact ⟨m, Algebra.leftMulMatrix_injective b hm⟩

theorem minpoly_dvd_P {K : UQ} (B : InvAlg K) : minpoly K.E B.g ∣ B.P := by
  have h1 : minpoly K.E (Algebra.lmul K.E B.A B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  rw [← h1]
  exact LinearMap.minpoly_dvd_charpoly _

theorem eq_zero_of_trace_mul_eq_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) →
    ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by
  intro K B hP hgen w hw
  obtain ⟨m, hm⟩ := isNilpotent_of_trace_mul w hw
  obtain ⟨f, rfl⟩ := hgen w
  have hd : minpoly K.E B.g ∣ f ^ m := minpoly.dvd K.E B.g (by rw [map_pow]; exact hm)
  have hsq : Squarefree (minpoly K.E B.g) := (hP.of_dvd (minpoly_dvd_P B)).squarefree
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    rw [pow_zero] at hm
    exact (subsingleton_of_zero_eq_one hm.symm).elim _ _
  have hf : minpoly K.E B.g ∣ f := (hsq.dvd_pow_iff_dvd h0.ne').mp hd
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma.TraceNondeg
