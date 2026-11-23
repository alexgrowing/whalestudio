import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial

theorem adjoinRoot_uniformiser_isDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  intro R _ _ _ π e hπ he _
  set f : R[X] := X ^ e - C π with hf
  have hmon : f.Monic := monic_X_pow_sub_C π he.ne'
  have hdeg : f.natDegree = e := natDegree_X_pow_sub_C
  haveI : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hmon).finite
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R _
  haveI : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite R _
  set x : AdjoinRoot f := AdjoinRoot.root f with hx
  have hxe : x ^ e = algebraMap R (AdjoinRoot f) π := by
    have h0 : AdjoinRoot.mk f f = 0 := AdjoinRoot.mk_self
    rw [hf, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  have hinj : Function.Injective (algebraMap R (AdjoinRoot f)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (by
      rw [degree_eq_natDegree hmon.ne_zero, hdeg]; exact_mod_cast he.ne')

  have hdec : ∀ a : AdjoinRoot f, ∃ r : R, ∃ y : AdjoinRoot f, a = algebraMap R _ r + x * y := by
    intro a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    refine ⟨p.coeff 0, AdjoinRoot.mk f p.divX, ?_⟩
    conv_lhs => rw [← X_mul_divX_add p]
    rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_comm]
    rfl
  have hπm : π ∈ maximalIdeal R := (mem_maximalIdeal _).2 hπ.not_isUnit

  have hcomap : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal →
      M.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R := fun M hM =>
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hxM : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal → x ∈ M := by
    intro M hM
    have : algebraMap R _ π ∈ M := by
      rw [← Ideal.mem_comap, hcomap M hM]; exact hπm
    rw [← hxe] at this
    exact hM.isPrime.mem_of_pow_mem e this
  have hle : ∀ M N : Ideal (AdjoinRoot f), M.IsMaximal → N.IsMaximal → M ≤ N := by
    intro M N hM hN a ha
    obtain ⟨r, y, rfl⟩ := hdec a
    have hr : algebraMap R _ r ∈ M := by
      have := M.sub_mem ha (M.mul_mem_right y (hxM M hM))
      simpa using this
    have hr' : r ∈ maximalIdeal R := by rw [← hcomap M hM]; exact hr
    have hrN : algebraMap R _ r ∈ N := by
      rw [← Ideal.mem_comap, hcomap N hN]; exact hr'
    exact N.add_mem hrN (N.mul_mem_right y (hxM N hN))
  haveI : IsLocalRing (AdjoinRoot f) :=
    IsLocalRing.of_unique_max_ideal (by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (AdjoinRoot f)
      exact ⟨M, hM, fun N hN => le_antisymm (hle N M hN hM) (hle M N hM hN)⟩)
  have hmax : maximalIdeal (AdjoinRoot f) = Ideal.span {x} := by
    apply le_antisymm
    · intro a ha
      obtain ⟨r, y, rfl⟩ := hdec a
      have hr : algebraMap R _ r ∈ maximalIdeal (AdjoinRoot f) := by
        have := Ideal.sub_mem (maximalIdeal (AdjoinRoot f)) ha
          (Ideal.mul_mem_right y (maximalIdeal (AdjoinRoot f)) (hxM _ (maximalIdeal.isMaximal _)))
        simpa using this
      have hr' : r ∈ maximalIdeal R := by
        rw [← hcomap _ (maximalIdeal.isMaximal _)]; exact hr
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at hr'
      obtain ⟨s, rfl⟩ := hr'
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      rw [map_mul, ← hxe, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self x he.ne') _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hxM _ (maximalIdeal.isMaximal _)
  have hx0 : x ≠ 0 := by
    intro h0
    have : algebraMap R (AdjoinRoot f) π = 0 := by rw [← hxe, h0, zero_pow he.ne']
    exact hπ.ne_zero (hinj (by rw [this, map_zero]))
  have hnf : ¬ IsField (AdjoinRoot f) := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hx0
    exact (mem_maximalIdeal x).1 (hxM _ (maximalIdeal.isMaximal _)) (IsUnit.of_mul_eq_one b hb)
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 4 0).1 (show (maximalIdeal (AdjoinRoot f)).IsPrincipal from ⟨⟨x, hmax⟩⟩)

end GlobalTheory
