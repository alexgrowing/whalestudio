import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPieceRootProductPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPieceCoefficientsHolomorphic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StMonicRootGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StGrowthOffHypersurfacePolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

theorem PieceRootProductPolynomial.coeff_bound {ι : Type*} (s : Finset ι) (r : ι → ℂ) (B : ℝ)
    (hB : ∀ x ∈ s, ‖r x‖ ≤ B) (i : ℕ) :
    ‖(∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).coeff i‖ ≤ B ^ (s.card - i) * (s.card.choose i) := by
  have hm : (∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _)
  have hdeg : (∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).natDegree = s.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _),
      Finset.sum_congr rfl (fun x _ => Polynomial.natDegree_X_sub_C _), Finset.sum_const, smul_eq_mul, mul_one]
  have hs : Polynomial.Splits ((∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).map (RingHom.id ℂ)) := by
    rw [Polynomial.map_id]
    exact Polynomial.Splits.prod (fun x _ => Polynomial.Splits.X_sub_C _)
  have h := Polynomial.coeff_le_of_roots_le (f := RingHom.id ℂ) (B := B) i hm hs (by
    intro z hz
    rw [Polynomial.map_id] at hz
    have hz' := (Polynomial.mem_roots hm.ne_zero).1 hz
    rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz'
    obtain ⟨x, hx, hx0⟩ := hz'
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hx0
    rw [hx0]
    exact hB x hx)
  rwa [Polynomial.map_id, hdeg] at h

theorem PieceRootProductPolynomial.coeff_monic_of_coeffs {R : Type*} [CommRing R] (k : ℕ) (p : ℕ → R)
    (i : ℕ) :
    (Polynomial.X ^ k + ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ)).coeff i =
      if i < k then p i else if i = k then 1 else 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hi : i < k
  · rw [Finset.sum_eq_single ⟨i, hi⟩, if_neg hi.ne, if_pos rfl, if_pos hi, zero_add]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext h.symm)
    · simp
  · rw [Finset.sum_eq_zero, if_neg hi, add_zero]
    intro j _
    rw [if_neg]
    intro h
    exact hi (h ▸ j.isLt)

theorem PieceRootProductPolynomial.proof (h1 : PieceCoefficientsHolomorphic.Statement)
    (h2 : MonicRootGrowth.Statement) (h3 : GrowthOffHypersurfacePolynomial.Statement) :
    PieceRootProductPolynomial.Statement := by
  intro n d N k A Z c m Q O F hm hQ hroot hcov hO hF hOF hk
  have hhol := h1 n d N A Z c Q O F hcov hO hF hOF
  obtain ⟨C, M, hC⟩ := h2 d m hm
  have hfin : ∀ y : Fin d → ℂ, eval y Q ≠ 0 → {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.Finite :=
    fun y hy => (hcov y hy).1.subset (fun x hx => ⟨hx.1, hx.2.2⟩)

  have hprod : ∀ (y : Fin d → ℂ) (hy : eval y Q ≠ 0),
      (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}, (Polynomial.X - Polynomial.C (∑ j, c j * x j))) =
        ∏ x ∈ (hfin y hy).toFinset, (Polynomial.X - Polynomial.C (∑ j, c j * x j)) :=
    fun y hy => finprod_mem_eq_finite_toFinset_prod _ (hfin y hy)
  have hcard : ∀ (y : Fin d → ℂ) (hy : eval y Q ≠ 0), (hfin y hy).toFinset.card = k :=
    fun y hy => by rw [← Set.ncard_eq_toFinset_card _ (hfin y hy), hk y hy]

  have hgrowth : ∀ (i : ℕ) (y : Fin d → ℂ), eval y Q ≠ 0 →
      ‖(∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i‖ ≤
        ((k.choose i : ℝ) * |C| ^ (k - i)) * (1 + ‖y‖) ^ (M * (k - i)) := by
    intro i y hy
    rw [hprod y hy]
    have hb := PieceRootProductPolynomial.coeff_bound (hfin y hy).toFinset (fun x => ∑ j, c j * x j)
      (|C| * (1 + ‖y‖) ^ M) (fun x hx => by
        obtain ⟨hxZ, -, hxy⟩ := (Set.Finite.mem_toFinset _).1 hx
        have h := hC y _ (hxy ▸ hroot x hxZ)
        exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) i
    rw [hcard y hy] at hb
    calc _ ≤ _ := hb
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hp : ∀ i : ℕ, ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i = eval y p :=
    fun i => h3 d Q _ _ _ hQ (hhol i) (hgrowth i)
  choose p hp using hp
  refine ⟨Polynomial.X ^ k + ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_, fun y hy => ?_⟩
  · rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt _
  · have hmon : (∏ x ∈ (hfin y hy).toFinset, (Polynomial.X - Polynomial.C (∑ j, c j * x j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _)
    have hdeg : (∏ x ∈ (hfin y hy).toFinset,
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).natDegree = k := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _),
        Finset.sum_congr rfl (fun x _ => Polynomial.natDegree_X_sub_C _), Finset.sum_const, smul_eq_mul,
        mul_one, hcard y hy]
    ext i
    rw [Polynomial.coeff_map, PieceRootProductPolynomial.coeff_monic_of_coeffs]
    by_cases hi : i < k
    · rw [if_pos hi, hp i y hy]
    · rw [if_neg hi, hprod y hy]
      by_cases hik : i = k
      · rw [if_pos hik, map_one, hik, ← hdeg]
        exact hmon.coeff_natDegree.symm
      · rw [if_neg hik, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

end GroundTheory.Heights₂.Heights.HilbertSamuel
