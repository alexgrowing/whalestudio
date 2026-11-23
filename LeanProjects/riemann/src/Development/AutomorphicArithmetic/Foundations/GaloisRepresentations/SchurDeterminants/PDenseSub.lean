import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem denseSub : DenseSub := by
  intro K σ _ _ _ L a hL Q hQ
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have hx : x - a ∈ Submodule.span K (L : Set (σ → K)) := by
    rw [hL]
    exact Submodule.mem_top
  obtain ⟨n, c, v, hcv⟩ := Submodule.mem_span_set'.mp hx
  let p0 : (Fin n → K) → σ → K := fun t j => a j + ∑ i, t i * (v i : σ → K) j
  let F : σ → MvPolynomial (Fin n) K := fun j => C (a j) + ∑ i, X i * C ((v i : σ → K) j)
  have hev : ∀ t, eval t (bind₁ F Q) = eval (p0 t) Q := by
    intro t
    have h1 : aeval t (bind₁ F Q) = eval t (bind₁ F Q) := rfl
    have h2 : aeval (fun j => aeval t (F j)) Q = eval (fun j => aeval t (F j)) Q := rfl
    rw [← h1, aeval_bind₁, h2]
    congr 2
    funext j
    simp [p0, F]
  have hzero : bind₁ F Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → K)) ?_ ?_
    · intro _
      exact Set.infinite_range_of_injective Int.cast_injective
    · intro t ht
      rw [hev, map_zero]
      choose m hm using fun i => ht i (Set.mem_univ i)
      apply hQ
      show p0 t - a ∈ L
      have hsum : p0 t - a = ∑ i, m i • (v i : σ → K) := by
        funext j
        simp [p0, ← hm, Finset.sum_apply, zsmul_eq_mul]
      rw [hsum]
      exact sum_mem (fun i _ => zsmul_mem (v i).2 (m i))
  have hxp : p0 c = x := by
    funext j
    have hj := congrFun hcv j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hj
    simp only [p0, hj]
    ring
  rw [← hxp, ← hev, hzero, map_zero]

end UpperTheory.Gal.Schur
