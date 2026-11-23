import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

noncomputable section

open Formalism.BasicNotions GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem tor_isUp (a k : ℕ) (z : Circle) : IsUp (tor a k z) := by
  intro i j hij
  rw [tor_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

private theorem circ_mul_conj (z : Circle) : (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

private theorem tor_unitary (a k : ℕ) (z : Circle) :
    ∃ u : Matrix.unitaryGroup (Fin a) ℂ, unitaryIncl a u = tor a k z := by
  set d : Fin a → ℂ := fun i => if (i : ℕ) < k then (z : ℂ) else 1 with hd
  have hdd : ∀ i, d i * (starRingEnd ℂ) (d i) = 1 := by
    intro i
    simp only [hd]
    split_ifs
    · rw [mul_comm]
      exact circ_mul_conj z
    · simp
  have hmem : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdd i
  refine ⟨⟨Matrix.diagonal d, hmem⟩, ?_⟩
  ext : 1
  rw [unitaryIncl_coe, tor_coe]

private theorem tor_chi {a : ℕ} (k : ℕ) (z : Circle) (κ : DomWeight a) :
    chi κ (tor a k z) = (z : ℂ) ^ psum κ k := by
  have hz : (z : ℂ) ≠ 0 := by simp
  simp only [chi, psum, tor_coe, Matrix.diagonal_apply_eq]
  rw [Finset.sum_filter]
  have key : ∀ s : Finset (Fin a), ∏ i ∈ s, (if (i : ℕ) < k then (z : ℂ) else 1) ^ κ.w i =
      (z : ℂ) ^ ∑ i ∈ s, (if (i : ℕ) < k then κ.w i else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hz]
      split_ifs <;> simp
  exact key _

private theorem tor_conj (a k : ℕ) (z : Circle) :
    Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (tor a k z) = tor a k z⁻¹ := by
  have hinv : (starRingEnd ℂ) (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv]
    exact eq_inv_of_mul_eq_one_left (circ_mul_conj z)
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, tor_coe, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [hinv]

theorem torFacts_of : TorFacts := fun a k z =>
  ⟨tor_isUp a k z, tor_unitary a k z, fun κ => tor_chi k z κ, tor_conj a k z⟩

end UpperTheory.Gal.Wt

end
