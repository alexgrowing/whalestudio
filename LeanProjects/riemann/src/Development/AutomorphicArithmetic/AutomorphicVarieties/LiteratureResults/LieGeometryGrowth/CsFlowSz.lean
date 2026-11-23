import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem norm_id_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (j : ℕ) (p : V) :
    ‖iteratedFDeriv ℝ (j + 1) (fun x : V => x) p‖ ≤ 1 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have e : fderiv ℝ (fun x : V => x) = fun _ => ContinuousLinearMap.id ℝ V := by
    funext x
    exact fderiv_id
  rw [e]
  rcases j with _ | j
  · simpa using ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simp

theorem UpperTheory.V.Lit.Geo.Cs.flowSz :
    FlowSz := by
  intro V _ _ k c W t p ht hW hS
  have e : UpperTheory.V.Lit.Geo.flow W t = (fun x : V => x) + t • W := rfl
  have h1 : ContDiffAt ℝ ∞ (UpperTheory.V.Lit.Geo.flow W t) p := by
    rw [e]
    exact contDiffAt_id.add (hW.const_smul t)
  have h4 : ∀ i, 1 ≤ i → i ≤ k + 1 → ‖iteratedFDeriv ℝ i (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    intro i h1i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hWj : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) W p := hW.of_le (by exact_mod_cast le_top)
    have hid : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun x : V => x) p := contDiffAt_id
    have htW : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (t • W) p := hWj.const_smul t
    rw [e, iteratedFDeriv_add_apply hid htW, iteratedFDeriv_const_smul_apply hWj]
    refine (norm_add_le _ _).trans (add_le_add (norm_id_le V j p) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (hS _ hi)
  refine ⟨h1, h1.fderiv_right (by simp), fun i hi => ?_, h4⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact h4 _ (by omega) (by omega)
