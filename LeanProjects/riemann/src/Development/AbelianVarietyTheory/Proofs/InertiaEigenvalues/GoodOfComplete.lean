import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.LAdic

def Good (p : ℕ) (R : Type) [CommRing R] : Prop :=
  (∀ x : R, (p : R) * x = 0 → x = 0) ∧ (∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → R, ∃ s, ∀ k : ℕ, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r

theorem good_of_complete (p : ℕ) (R : Type) [CommRing R] (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    [hc : IsAdicComplete (Ideal.span {(p : R)}) R] : Good p R := by
  have mem : ∀ (k : ℕ) (x : R), x ∈ (Ideal.span {(p : R)} ^ k • ⊤ : Submodule R R) ↔
      ∃ r, x = (p : R) ^ k * r := by
    intro k x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rfl
  refine ⟨h, fun x hx => ?_, fun x => ?_⟩
  · refine IsHausdorff.haus (I := Ideal.span {(p : R)}) hc.toIsHausdorff x fun k => ?_
    rw [SModEq.zero, mem]
    exact hx k
  · obtain ⟨s, hs⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) hc.toIsPrecomplete
      (f := fun k => ∑ i ∈ Finset.range k, (p : R) ^ i * x i) (by
        intro m n hmn
        rw [SModEq.sub_mem, mem]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        refine ⟨-∑ i ∈ Finset.range k, (p : R) ^ i * x (m + i), ?_⟩
        rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
        simp only [pow_add, mul_assoc]
        ring)
    refine ⟨s, fun k => ?_⟩
    have := (hs k).symm
    rwa [SModEq.sub_mem, mem] at this

theorem good_tensor {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
    (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W] (p : ℕ) (h : Good p W) :
    Good p (O ⊗[Z] W) := by
  have hp : ∀ (k : ℕ) (i : I) (x : O ⊗[Z] W),
      crd b i ((p : O ⊗[Z] W) ^ k * x) = (p : W) ^ k * crd b i x := by
    intro k i x
    rw [← Nat.cast_pow, crd_natCast_mul, Nat.cast_pow]
  refine ⟨fun x hx => ext_crd b fun i => ?_, fun x hx => ext_crd b fun i => ?_, fun x => ?_⟩
  · rw [map_zero]
    apply h.1
    rw [← crd_natCast_mul, hx, map_zero]
  · rw [map_zero]
    refine h.2.1 _ fun k => ?_
    obtain ⟨r, hr⟩ := hx k
    exact ⟨crd b i r, by rw [← hp, ← hr]⟩
  · choose s r hs using fun i => h.2.2 fun k => crd b i (x k)
    refine ⟨∑ j, b j ⊗ₜ[Z] s j, fun k => ⟨∑ j, b j ⊗ₜ[Z] r j k, ext_crd b fun i => ?_⟩⟩
    rw [map_sub, hp, crd_sum, crd_sum b (fun j => r j k), map_sum, ← hs]
    simp only [hp]

theorem good_witt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Good p (WittVector p k) :=
  good_of_complete p _ fun x hx => WittVector.eq_zero_of_p_mul_eq_zero x (by rw [mul_comm]; exact hx)

theorem ladic_RW (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ x : RW LL, (l : RW LL) * x = 0 → x = 0) ∧
    (∀ x : RW LL, (∀ k : ℕ, ∃ r, x = (l : RW LL) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → RW LL, ∃ s, ∀ k : ℕ, ∃ r,
      s - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r :=
  good_tensor (W := WCb l) (basisO LL) l (good_witt l (Cb l))

end GlobalTheory.Decompl.LAdic
