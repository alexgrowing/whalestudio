import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimary

open Polynomial

namespace GlobalTheory.SepGen

variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]

theorem charpoly_dvd (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) (f : E[X])
    (hf : aeval y f = 0) : (LinearMap.mulLeft E y).charpoly ∣ f := by
  have h0 : aeval (LinearMap.mulLeft E y) f = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y f
    rw [hf, map_zero] at this
    exact this
  by_cases hz : f = 0
  · rw [hz]; exact dvd_zero _
  classical
  have hP := hs.ne_zero
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
    Multiset.le_iff_subset
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
  intro p hp
  rw [Polynomial.mem_normalizedFactors_iff hP] at hp
  rw [Polynomial.mem_normalizedFactors_iff hz]
  exact ⟨hp.1, hp.2.1,
    GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩

theorem aeval_charpoly (y : A) : aeval y (LinearMap.mulLeft E y).charpoly = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y (LinearMap.mulLeft E y).charpoly
  have h2 : aeval (Algebra.lmul E A y) (LinearMap.mulLeft E y).charpoly = 0 :=
    LinearMap.aeval_self_charpoly _
  rw [h2] at h
  simpa using (LinearMap.congr_fun h 1).symm

theorem adjoin_eq_top (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) :
    Algebra.adjoin E ({y} : Set A) = ⊤ := by
  have hi : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  have h1 := natDegree_le_of_dvd (charpoly_dvd y hs _ (minpoly.aeval E y)) (minpoly.ne_zero hi)
  rw [LinearMap.charpoly_natDegree] at h1
  have h2 : Module.finrank E (Algebra.adjoin E ({y} : Set A)) = (minpoly E y).natDegree :=
    (Algebra.adjoin.powerBasis hi).finrank
  have h3 : Subalgebra.toSubmodule (Algebra.adjoin E ({y} : Set A)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h1.trans h2.ge))
  rw [← Algebra.toSubmodule_eq_top]
  exact h3

theorem isReduced (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) : IsReduced A := by
  have h3 := adjoin_eq_top y hs
  refine ⟨fun z ⟨k, hk⟩ => ?_⟩
  have hz : z ∈ Algebra.adjoin E ({y} : Set A) := by rw [h3]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  have h4 := charpoly_dvd y hs (p ^ k) (by rw [map_pow]; exact hk)
  obtain ⟨r, hr⟩ := hs.squarefree.isRadical k p h4
  change aeval y p = 0
  rw [hr, map_mul, aeval_charpoly, zero_mul]

theorem adjoin_eq_top_and_isReduced : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable →
    Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A :=
  fun _ _ _ _ _ _ y hs => ⟨adjoin_eq_top y hs, isReduced y hs⟩

end GlobalTheory.SepGen
