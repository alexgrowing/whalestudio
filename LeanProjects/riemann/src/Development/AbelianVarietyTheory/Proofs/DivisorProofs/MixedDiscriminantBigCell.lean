import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigCell

theorem mix_blk_fib (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin (D + 1) ≃ Fin n ⊕ (Σ a, Low (r a)))
    (N : Matrix (Fin n) (Fin n) ℂ) (δ m : (Σ a, Low (r a)) → ℝ) :
    mix D (BigCell.blk ε N δ) (BigCell.blk ε 0 m) =
      (D.factorial : ℝ) / Real.pi ^ (D + 1) * N.det.re * ∑ s, m s * ∏ s' ∈ Finset.univ.erase s, δ s' := by
  set X : Matrix (Fin n ⊕ (Σ a, Low (r a))) (Fin n ⊕ (Σ a, Low (r a))) ℂ :=
    fromBlocks N 0 0 (diagonal fun s => (δ s : ℂ)) with hX
  have hY : (fromBlocks 0 0 0 (diagonal fun s => (m s : ℂ)) :
      Matrix (Fin n ⊕ (Σ a, Low (r a))) (Fin n ⊕ (Σ a, Low (r a))) ℂ) =
      diagonal (Sum.elim 0 fun s => (m s : ℂ)) := by
    rw [← fromBlocks_diagonal]
    simp
  have hadj : ∀ s, X.adjugate (Sum.inr s) (Sum.inr s) = N.det * ∏ s' ∈ Finset.univ.erase s, (δ s' : ℂ) := by
    intro s
    rw [adjugate_apply]
    have hu : X.updateRow (Sum.inr s) (Pi.single (Sum.inr s) 1) =
        fromBlocks N 0 0 (diagonal (Function.update (fun s => (δ s : ℂ)) s 1)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · simp [hX, updateRow_apply]
      · simp [hX, updateRow_apply]
      · by_cases h : i = s
        · subst h; simp [hX, updateRow_apply]
        · simp [hX, updateRow_apply, h]
      · by_cases h : i = s
        · subst h
          by_cases h' : j = i
          · subst h'; simp [hX, updateRow_apply]
          · simp [hX, updateRow_apply, diagonal_apply, h', Ne.symm h', Pi.single_apply]
        · by_cases h' : i = j
          · subst h'; simp [hX, updateRow_apply, h, diagonal_apply]
          · simp [hX, updateRow_apply, h, diagonal_apply, h']
    rw [hu, det_fromBlocks_zero₂₁, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ s), one_mul,
      Finset.sdiff_singleton_eq_erase]
  have htr : (X.adjugate * diagonal (Sum.elim 0 fun s => (m s : ℂ))).trace =
      ∑ s, (N.det * ∏ s' ∈ Finset.univ.erase s, (δ s' : ℂ)) * (m s : ℂ) := by
    rw [trace, Fintype.sum_sum_type]
    simp only [diag_apply, mul_diagonal, Sum.elim_inl, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
      Sum.elim_inr, hadj]
  have htrs : ∀ A : Matrix (Fin n ⊕ (Σ a, Low (r a))) (Fin n ⊕ (Σ a, Low (r a))) ℂ,
      (A.submatrix ε ε).trace = A.trace := fun A => by
    simp only [trace, diag_apply, submatrix_apply]
    exact Equiv.sum_comp ε fun i => A i i
  rw [mix, blk, blk, adjugate_submatrix_equiv_self, submatrix_mul_equiv, htrs, ← hX, hY, htr, Complex.re_sum, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Complex.ofReal_prod, mul_assoc, ← Complex.ofReal_mul, Complex.re_mul_ofReal]
  ring
end GlobalTheory.BigCell
