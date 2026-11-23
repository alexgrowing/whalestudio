import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
open UpperTheory.V.Lit.Geo

private theorem aux {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ} (A : F) (u : ℂ) (l : Fin (q + 1) → ℂ)
    (B : Fin (q + 1) → F) (n : Fin (q + 1) → ℝ) (s b M M' : ℝ) (hn : ∀ i, 0 ≤ n i) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hs : ‖1 - u‖ ≤ s) (hl : ∀ i, ‖l i‖ ≤ b * n i)
    (hB : b = 0 ∨ ∀ i, ‖B i‖ ≤ M * ∏ j, n (i.succAbove j)) (hA : ‖A‖ ≤ M' * ∏ i, n i) :
    ‖A - (u • A + ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i)‖ ≤ (s * M' + (q + 1) * b * M) * ∏ i, n i := by
  have hP : 0 ≤ ∏ i, n i := Finset.prod_nonneg fun i _ => hn i
  have e : A - (u • A + ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i) =
      (1 - u) • A - ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i := by
    rw [sub_smul, one_smul, sub_sub]
  have h1 : ‖(1 - u) • A‖ ≤ s * (M' * ∏ i, n i) := by
    rw [norm_smul]
    exact mul_le_mul hs hA (norm_nonneg _) ((norm_nonneg _).trans hs)
  have h2 : ∀ i : Fin (q + 1), ‖((-1 : ℂ) ^ (i : ℕ) * l i) • B i‖ ≤ b * M * ∏ i, n i := fun i => by
    rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rcases hB with h | h
    · have h0 : ‖l i‖ = 0 := le_antisymm (by simpa [h] using hl i) (norm_nonneg _)
      simp [h, h0]
    · refine (mul_le_mul (hl i) (h i) (norm_nonneg _) (mul_nonneg hb (hn i))).trans_eq ?_
      rw [Fin.prod_univ_succAbove n i]
      ring
  have h3 : ‖∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i‖ ≤ (q + 1) * (b * M * ∏ i, n i) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => h2 i).trans_eq ?_)
    simp
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add h1 h3).trans_eq ?_)
  ring

theorem UpperTheory.V.Lit.Geo.cutBd :
    CutBd := by
  intro E _ _ _ a Ξ q u η ζ h g s b M M' hM _ hb hs hl hη hd X
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, h]
  exact aux _ _ _ _ (fun i => ‖UpperTheory.V.Lit.Dr.hv (X i)‖) s b M M' (fun _ => norm_nonneg _) hM hb hs
    (fun i => hl _) (hη.imp id fun hη i => hη _) (hd X)
