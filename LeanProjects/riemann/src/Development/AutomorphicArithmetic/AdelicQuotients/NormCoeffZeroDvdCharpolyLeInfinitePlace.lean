import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private lemma norm_multiset_prod_le_pow (B : ℝ) (hB : 1 ≤ B) (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ B) : ‖s.prod‖ ≤ B ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    exact mul_le_mul (hs a (Multiset.mem_cons_self ..))
      (ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)) (norm_nonneg _) (by linarith)

private lemma norm_root_charpoly_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hM : ∀ i j, ‖M i j‖ ≤ R) (z : ℂ) (hz : M.charpoly.IsRoot z) :
    ‖z‖ ≤ max 1 (n : ℝ) * R := by
  have hdet : ((Matrix.scalar (Fin n)) z - M).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hz
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) ⟨i0, Finset.mem_univ _⟩
  have hvi : 0 < ‖v i‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi0) (hi i0 (Finset.mem_univ _))
  have hrow : z * v i = ∑ j, M i j * v j := by
    have h1 := congrFun hMv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1
    have h2 : ((Matrix.scalar (Fin n)) z).mulVec v i = z * v i := by
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [h2] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  have hle : ‖z‖ * ‖v i‖ ≤ n * R * ‖v i‖ := by
    rw [← norm_mul, hrow]
    calc ‖∑ j, M i j * v j‖ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, R * ‖v i‖ := Finset.sum_le_sum (fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (hM i j) (hi j (Finset.mem_univ _)) (norm_nonneg _) (by linarith))
      _ = n * R * ‖v i‖ := by simp [Finset.sum_const, mul_assoc]
  have h3 : ‖z‖ ≤ n * R := le_of_mul_le_mul_right hle hvi
  exact h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

private lemma norm_coeff_zero_le_complex {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hM : ∀ i j, ‖M i j‖ ≤ R) (p : ℂ[X]) (hp : p.Monic) (hd : p ∣ M.charpoly) :
    ‖p.coeff 0‖ ≤ (max 1 (n : ℝ) * R) ^ n := by
  have hB : 1 ≤ max 1 (n : ℝ) * R := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hR
  have hs : p.Splits := IsAlgClosed.splits p
  have hc : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  rw [hs.coeff_zero_eq_prod_roots_of_monic hp, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  have hroots : ∀ z ∈ p.roots, ‖z‖ ≤ max 1 (n : ℝ) * R := fun z hz =>
    norm_root_charpoly_le M R hR hM z ((Polynomial.isRoot_of_mem_roots hz).dvd hd)
  refine (norm_multiset_prod_le_pow _ hB _ hroots).trans ?_
  rw [← hs.natDegree_eq_card_roots]
  refine pow_le_pow_right₀ hB ?_
  have h := natDegree_le_of_dvd hd hc
  simpa [Matrix.charpoly_natDegree_eq_dim] using h

theorem UpperTheory.norm_coeff_zero_dvd_charpoly_le_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E) (n : ℕ) (M : Matrix (Fin n) (Fin n) w.Completion) (R : ℝ), 1 ≤ R →
        (∀ i j, ‖M i j‖ ≤ R) → ∀ p : w.Completion[X], p.Monic → p ∣ M.charpoly → ‖p.coeff 0‖ ≤ (max 1 (n : ℝ) * R) ^ n := by
  intro E _ _ w n M R hR hM p hp hd
  have hn : ∀ x, ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
  have h := norm_coeff_zero_le_complex (M.map (InfinitePlace.Completion.extensionEmbedding w)) R hR
    (fun i j => by simpa [hn] using hM i j)
    (p.map (InfinitePlace.Completion.extensionEmbedding w))
    (hp.map _)
    (by rw [Matrix.charpoly_map]; exact Polynomial.map_dvd _ hd)
  rwa [coeff_map, hn] at h
