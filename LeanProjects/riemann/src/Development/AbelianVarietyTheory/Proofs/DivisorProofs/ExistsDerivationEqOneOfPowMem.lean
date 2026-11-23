import Mathlib
open TensorProduct

namespace GlobalTheory

open Polynomial

theorem exists_derivation_eq_one_of_pow_mem : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (L : Subfield K) (f : K), f ∉ L → f ^ p ∈ L → IntermediateField.adjoin L ({f} : Set K) = ⊤ → ∃ D : Derivation L K K, D f = 1 := by
  intro p hp K _ _ L f hfL hfp htop
  have hpp : p.Prime := hp.out
  set a : L := ⟨f ^ p, hfp⟩ with ha
  set q : Polynomial L := X ^ p - C a with hq
  have hqf : aeval f q = 0 := by
    rw [hq, map_sub, map_pow, aeval_X, aeval_C]
    exact sub_eq_zero.mpr rfl
  have hirr : Irreducible q := by
    apply X_pow_sub_C_irreducible_of_prime hpp
    intro b hb
    apply hfL
    have h1 : (b : K) ^ p = f ^ p := by
      have := congrArg (fun x : L => (x : K)) hb
      simpa [a] using this
    have h2 : (b : K) = f := frobenius_inj K p h1
    exact h2 ▸ b.2
  have hmon : q.Monic := monic_X_pow_sub_C a hpp.ne_zero
  have hmin : minpoly L f = q := (minpoly.eq_of_irreducible_of_monic hirr hqf hmon).symm
  have hdq : aeval f (derivative q) = 0 := by
    simp [q, derivative_X_pow]
  have hker : ∀ g : Polynomial L, aeval f g = 0 → aeval f (derivative g) = 0 := by
    intro g hg
    obtain ⟨h, rfl⟩ : q ∣ g := hmin ▸ minpoly.dvd L f hg
    simp [derivative_mul, hdq, hqf]
  have hint : IsIntegral L f := ⟨q, hmon, hqf⟩
  have hsurj : ∀ x : K, ∃ g : Polynomial L, aeval f g = x := by
    intro x
    have hx : x ∈ Algebra.adjoin L ({f} : Set K) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).mp hx
  choose G hG using hsurj
  have hwd : ∀ g1 g2 : Polynomial L, aeval f g1 = aeval f g2 →
      aeval f (derivative g1) = aeval f (derivative g2) := by
    intro g1 g2 h
    have := hker (g1 - g2) (by rw [map_sub, h, sub_self])
    rwa [derivative_sub, map_sub, sub_eq_zero] at this
  let Dl : K →ₗ[L] K :=
    { toFun := fun x => aeval f (derivative (G x))
      map_add' := fun x y => by
        rw [← map_add, ← derivative_add]
        apply hwd
        rw [hG, map_add, hG, hG]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← map_smul (aeval f), ← map_smul derivative]
        apply hwd
        rw [hG, map_smul, hG] }
  refine ⟨Derivation.mk' Dl (fun x y => ?_), ?_⟩
  · show aeval f (derivative (G (x * y))) = x • aeval f (derivative (G y)) + y • aeval f (derivative (G x))
    rw [hwd (G (x * y)) (G x * G y) (by rw [hG, map_mul, hG, hG]), derivative_mul, map_add, map_mul, map_mul, hG, hG, smul_eq_mul, smul_eq_mul]
    ring
  · show aeval f (derivative (G f)) = 1
    rw [hwd (G f) X (by rw [hG, aeval_X]), derivative_X, map_one]

end GlobalTheory
