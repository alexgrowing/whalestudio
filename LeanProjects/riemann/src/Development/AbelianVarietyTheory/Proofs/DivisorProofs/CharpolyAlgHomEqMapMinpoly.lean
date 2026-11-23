import Mathlib
import GroundTheory.Brauer.TensorSimple
open scoped TensorProduct

namespace GlobalTheory.CsaCharpoly
open Polynomial

theorem injective_of_isSimpleRing {R S : Type} [Ring R] [IsSimpleRing R] [Ring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f := by
  rcases eq_bot_or_eq_top (TwoSidedIdeal.ker f) with h | h
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ TwoSidedIdeal.ker f := (TwoSidedIdeal.mem_ker f).2 hx
    rw [h] at this
    simpa using this
  · exfalso
    have : (1 : R) ∈ TwoSidedIdeal.ker f := by rw [h]; trivial
    rw [TwoSidedIdeal.mem_ker, map_one] at this
    exact one_ne_zero this

theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end GlobalTheory.CsaCharpoly

namespace GlobalTheory
open Polynomial

theorem charpoly_algHom_eq_map_minpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ),
    Module.finrank F C = n ^ 2 → ∀ (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    (minpoly F y).natDegree = n → (ι y).charpoly = (minpoly F y).map (algebraMap F L) := by
  intro F L C _ _ _ _ _ _ _ _ n _ ι a hdeg
  have ha : IsIntegral F a := IsIntegral.of_finite F a
  have hn : 0 < n := hdeg ▸ minpoly.natDegree_pos ha
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hxi : IsIntegral L (ι a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have hge : n ≤ (minpoly L (ι a)).natDegree := by
    rw [hmin, ← hdeg]; exact GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  have hdvd : minpoly L (ι a) ∣ (minpoly F a).map (algebraMap F L) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmonic : ((minpoly F a).map (algebraMap F L)).Monic := (minpoly.monic ha).map _
  have hdm : ((minpoly F a).map (algebraMap F L)).natDegree = n := by rw [natDegree_map, hdeg]
  have e1 : (minpoly F a).map (algebraMap F L) = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hmonic hdvd (by rw [hdm]; exact hge)
  have e2 : (ι a).charpoly = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hge)
  rw [e2, e1]

end GlobalTheory
