import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IwasawaDecompositionRealMatrixStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DetLeadingMinorGramIwasawaStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegralStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnipotentUpperSizeReductionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramMinorSwapAdjacentColumnsStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HermiteReduction

theorem exists_lt_two_mul {S : Type} [Nonempty S] (f : S → ℝ) (c : ℝ) (hc : 0 < c) (hf : ∀ s, c ≤ f s) :
    ∃ s, ∀ t, f s < 2 * f t := by
  have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have hm : c ≤ ⨅ s, f s := le_ciInf hf
  have hlt : ⨅ s, f s < 2 * ⨅ s, f s := by linarith
  obtain ⟨s, hs⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨s, fun t => hs.trans_le (by linarith [ciInf_le hbdd t])⟩

noncomputable def gramMinor {N : ℕ} (x : Matrix (Fin N) (Fin N) ℝ) (j : Fin (N + 1)) : ℝ :=
  ((xᵀ * x).submatrix (Fin.castLE (Nat.lt_succ_iff.mp j.2)) (Fin.castLE (Nat.lt_succ_iff.mp j.2))).det

theorem prod_castLE_succ {N : ℕ} (f : Fin N → ℝ) (p q : Fin N) (hq : (q : ℕ) = p + 1) (h : (q : ℕ) ≤ N) :
    ∏ i : Fin q, f (Fin.castLE h i) = (∏ l ∈ Finset.univ.filter (· < p), f l) * f p := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq'⟩ := q
  simp only at hq h ⊢
  subst hq
  rw [Fin.prod_univ_castSucc]
  congr 1
  refine Finset.prod_bij (fun i _ => Fin.castLE h i.castSucc) ?_ ?_ ?_ ?_
  · intro i _
    simp [Fin.lt_def]
  · intro i _ j _ hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)
  · intro l hl
    have hl' : (l : ℕ) < p := by simpa [Fin.lt_def] using hl
    exact ⟨⟨l, hl'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

theorem mul_upper {N : ℕ} (n m : Matrix (Fin N) (Fin N) ℝ) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hm1 : ∀ i, m i i = 1) (hm0 : ∀ i j, j < i → m i j = 0) :
    (∀ i, (n * m) i i = 1) ∧ ∀ i j, j < i → (n * m) i j = 0 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hn1, hm1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hn0 i l h, zero_mul]
      · rw [hm0 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hn0 i l h, zero_mul]
    · rw [hm0 l j (lt_of_lt_of_le hij h), mul_zero]

theorem le_of_swap {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hν : ∀ i j, i < j → |n i j| ≤ 1 / 2) (p q : Fin N) (hq : (q : ℕ) = p + 1)
    (hlt : ∏ j, gramMinor (k * diagonal a * n) j <
      2 * ∏ j, gramMinor ((k * diagonal a * n).submatrix id (Equiv.swap p q)) j) : a p ≤ 2 * a q := by
  set g := k * diagonal a * n with hg
  have hpq : p < q := by rw [Fin.lt_def]; omega
  have hqN : (q : ℕ) ≤ N := q.2.le
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gram_minor_swap_adjacent_columns N k a n g (g.submatrix id (Equiv.swap p q)) p q hk hn1 hn0 hq rfl rfl
  have hG : ∀ j : Fin (N + 1),
      gramMinor g j = ∏ i : Fin j, a (Fin.castLE (Nat.lt_succ_iff.mp j.2) i) ^ 2 :=
    fun j => GlobalTheory.T.det_leading_minor_gram_iwasawa N k a n hk hn1 hn0 j _
  let qq : Fin (N + 1) := ⟨q, Nat.lt_succ_of_le hqN⟩
  have hpos : ∀ j, 0 < gramMinor g j := fun j => by
    rw [hG]
    exact Finset.prod_pos fun i _ => pow_pos (ha _) 2
  have hrest : ∏ j ∈ Finset.univ.erase qq, gramMinor (g.submatrix id (Equiv.swap p q)) j =
      ∏ j ∈ Finset.univ.erase qq, gramMinor g j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ q := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    exact h1 j (Nat.lt_succ_iff.mp j.2) hne
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ qq),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ qq), hrest] at hlt
  have hR : 0 < ∏ j ∈ Finset.univ.erase qq, gramMinor g j := Finset.prod_pos fun j _ => hpos j
  have hlt' : gramMinor g qq < 2 * gramMinor (g.submatrix id (Equiv.swap p q)) qq := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_right hc' hR.le]
  have eG : gramMinor g qq = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * a p ^ 2 := by
    rw [hG]
    exact prod_castLE_succ (fun i => a i ^ 2) p q hq _
  have eG' : gramMinor (g.submatrix id (Equiv.swap p q)) qq =
      (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := h2 hqN
  rw [eG, eG'] at hlt'
  have hP : 0 < ∏ l ∈ Finset.univ.filter (· < p), a l ^ 2 :=
    Finset.prod_pos fun l _ => pow_pos (ha l) 2
  have hn : n p q ^ 2 ≤ 1 / 4 := by
    have h3 := abs_le.mp (hν p q hpq)
    nlinarith [h3.1, h3.2]
  have key : a p ^ 2 < 2 * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hP.le]
  have hap := ha p
  have haq := ha q
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [mul_lt_mul'' hc' hc' (by positivity) (by positivity),
    mul_le_mul_of_nonneg_right hn (sq_nonneg (a p))]

theorem exists_reduced : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (γ : Matrix (Fin N) (Fin N) ℤ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ (∀ i j, i < j → |n i j| ≤ 1 / 2) ∧ (∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  intro N g hg
  obtain ⟨c, hc, hcb⟩ := GlobalTheory.T.gram_leading_minor_lower_bound_integral N g hg
  let S := {γ : Matrix (Fin N) (Fin N) ℤ // γ.det = 1 ∨ γ.det = -1}
  have : Nonempty S := ⟨⟨1, Or.inl Matrix.det_one⟩⟩
  have hdet0 : ∀ γ : S, γ.1.det ≠ 0 := fun γ => by
    rcases γ.2 with h | h <;> rw [h] <;> norm_num
  have hbound : ∀ γ : S, c ^ (N + 1) ≤ ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j := by
    intro γ
    calc c ^ (N + 1) = ∏ _j : Fin (N + 1), c := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hc.le)
          (fun j _ => hcb γ.1 (hdet0 γ) j (Nat.lt_succ_iff.mp j.2))
  obtain ⟨γ0, hγ0⟩ := exists_lt_two_mul
    (fun γ : S => ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j) (c ^ (N + 1)) (pow_pos hc _) hbound
  have hgd : (g * γ0.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero hg ?_
    rw [← Int.cast_det]
    exact_mod_cast hdet0 γ0
  obtain ⟨k, a, n, hk, ha, hn1, hn0, hgk⟩ := GlobalTheory.T.iwasawa_decomposition_real_matrix N _ hgd
  obtain ⟨ν, hν1, hν0, hνb⟩ := GlobalTheory.T.unipotent_upper_size_reduction N n hn1 hn0
  have hνR1 : ∀ i, ν.map (Int.cast : ℤ → ℝ) i i = 1 := fun i => by simp [hν1]
  have hνR0 : ∀ i j, j < i → ν.map (Int.cast : ℤ → ℝ) i j = 0 := fun i j h => by simp [hν0 i j h]
  obtain ⟨hn'1, hn'0⟩ := mul_upper n _ hn1 hn0 hνR1 hνR0
  have hνdet : ν.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hν0 i j h)]
    simp [hν1]
  have hγdet : (γ0.1 * ν).det = 1 ∨ (γ0.1 * ν).det = -1 := by
    rw [Matrix.det_mul, hνdet, mul_one]
    exact γ0.2
  have hmap : (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      γ0.1.map (Int.cast : ℤ → ℝ) * ν.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have heq : g * (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ)) := by
    rw [hmap, ← Matrix.mul_assoc, hgk, Matrix.mul_assoc (k * diagonal a)]
  have hΦ : ∏ j, gramMinor (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))) j =
      ∏ j, gramMinor (g * γ0.1.map (Int.cast : ℤ → ℝ)) j := by
    rw [hgk]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold gramMinor
    rw [GlobalTheory.T.det_leading_minor_gram_iwasawa N k a _ hk hn'1 hn'0 j _, GlobalTheory.T.det_leading_minor_gram_iwasawa N k a n hk hn1 hn0 j _]
  refine ⟨γ0.1 * ν, k, a, n * ν.map (Int.cast : ℤ → ℝ), hγdet, hk, ha, hn'1, hn'0, hνb,
    fun p q hq => ?_, heq⟩
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  let γ' : S := ⟨(γ0.1 * ν).submatrix id (Equiv.swap p q), by
    rw [Matrix.det_permute', Equiv.Perm.sign_swap hpq]
    rcases hγdet with h | h <;> simp [h]⟩
  have hsw : g * γ'.1.map (Int.cast : ℤ → ℝ) =
      (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))).submatrix id (Equiv.swap p q) := by
    rw [← heq]
    ext i j
    rfl
  refine le_of_swap k a _ hk ha hn'1 hn'0 hνb p q hq ?_
  rw [hΦ, ← hsw]
  exact hγ0 γ'

end GlobalTheory.ClassFin.HermiteReduction
