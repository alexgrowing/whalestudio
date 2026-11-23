import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.DetCoef

theorem det_add_smul_eq_sum {n : Type} [Fintype n] [DecidableEq n] (Θ N : Matrix n n ℂ) (t : ℂ) :
    (Θ + t • N).det = ∑ S : Finset n, t ^ S.card * Matrix.det (Matrix.of (S.piecewise N Θ)) := by
  have h := (Matrix.detRowAlternating (n := n) (R := ℂ)).toMultilinearMap.map_add_univ (t • N) Θ
  rw [add_comm Θ]
  refine h.trans (Finset.sum_congr rfl fun S _ => ?_)
  have h2 := (Matrix.detRowAlternating (n := n) (R := ℂ)).toMultilinearMap.map_piecewise_smul
    (fun _ => t) (S.piecewise N Θ) S
  rw [Finset.prod_const, smul_eq_mul] at h2
  refine Eq.trans ?_ h2
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [Finset.piecewise, hi]; rfl
  · simp [Finset.piecewise, hi]

theorem trace_adjugate_mul {n : Type} [Fintype n] [DecidableEq n] (Θ N : Matrix n n ℂ) :
    (N.adjugate * Θ).trace = ∑ k, (N.updateRow k (Θ k)).det := by
  rw [Matrix.trace_mul_comm, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem sum_card_eq {e : ℕ} {M : Type} [AddCommMonoid M] (d : Finset (Fin (e + 1)) → M) :
    ∑ S : Finset (Fin (e + 1)), (if S.card = e then d S else 0) = ∑ k, d (Finset.univ.erase k) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun k _ => Finset.univ.erase k) ?_ ?_ ?_ ?_
  · intro k _
    simp [Finset.card_erase_of_mem]
  · intro a _ b _ h
    by_contra hab
    have : a ∈ Finset.univ.erase b := by simp [hab]
    rw [← h] at this
    simp at this
  · intro S hS
    have hS' : S.card = e := by simpa using hS
    have h1 : Sᶜ.card = 1 := by rw [Finset.card_compl, hS']; simp
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 h1
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [← compl_compl S, hk, Finset.compl_singleton]
  · intro _ _; rfl

theorem coeff_compare :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (Λ : R →ₗ[ℝ] ℝ) (a b : R) (f e : ℕ) (Θ N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : ℝ), (∀ t : ℝ, Λ ((a + t • b) ^ (f + e)) = s * (Θ + (t : ℂ) • N).det.re) → ((f + e).choose e : ℝ) * Λ (a ^ f * b ^ e) = s * (N.adjugate * Θ).trace.re := by
  intro R _ _ Λ a b f e Θ N s h
  let c : ℕ → ℝ := fun m => ((f + e).choose m : ℝ) * Λ (a ^ (f + e - m) * b ^ m)
  let d : Finset (Fin (e + 1)) → ℝ := fun S => s * (Matrix.det (Matrix.of (S.piecewise N Θ))).re
  have hP : (∑ m ∈ Finset.range (f + e + 1), Polynomial.monomial m (c m)) =
      ∑ S : Finset (Fin (e + 1)), Polynomial.monomial S.card (d S) := by
    apply Polynomial.funext
    intro t
    have ht := h t
    rw [det_add_smul_eq_sum, add_comm a, add_pow, map_sum, Complex.re_sum, Finset.mul_sum] at ht
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    refine Eq.trans ?_ (ht.trans ?_)
    · refine Finset.sum_congr rfl fun m _ => ?_
      have : (t • b) ^ m * a ^ (f + e - m) * ((f + e).choose m : R) =
          (((f + e).choose m : ℝ) * t ^ m) • (a ^ (f + e - m) * b ^ m) := by
        rw [smul_pow, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, smul_mul_assoc, mul_comm (b ^ m), mul_comm]
      rw [this, map_smul, smul_eq_mul]
      simp only [c]; ring
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
      simp only [d]; ring
  have hc := congrArg (fun p => Polynomial.coeff p e) hP
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial] at hc
  rw [sum_card_eq, Finset.sum_ite_eq' , if_pos (by simp)] at hc
  simp only [c, Nat.add_sub_cancel] at hc
  rw [hc, trace_adjugate_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [d]
  congr 3
  ext i j
  by_cases hi : i = k
  · subst hi; simp [Finset.piecewise]
  · simp [Finset.piecewise, hi]

end GlobalTheory.DetCoef
