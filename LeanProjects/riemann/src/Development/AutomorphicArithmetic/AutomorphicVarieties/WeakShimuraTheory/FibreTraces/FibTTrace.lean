import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply

open Polynomial UpperTheory.V.GradeZeroInterpolatingElement

private theorem det_mem_subfield_of_entries_mem {K : Type} [Field K] (E : Subfield K) (M : Matrix (Fin 4) (Fin 4) K)
    (hM : ∀ i j, M i j ∈ E) : M.det ∈ E := by
  rw [Matrix.det_apply]
  refine E.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact E.zsmul_mem (E.prod_mem fun i _ => hM _ _) _

private theorem mem_subfield_of_vandermonde_sums_mem {K : Type} [Field K] (E : Subfield K) (d x : Fin 4 → K)
    (hd : Function.Injective d) (hdE : ∀ i, d i ∈ E)
    (h : ∀ b : Fin 4, ∑ j, d j ^ (b : ℕ) * x j ∈ E) : ∀ j, x j ∈ E := by
  set V : Matrix (Fin 4) (Fin 4) K := Matrix.of fun b k => d k ^ (b : ℕ) with hV
  have hVE : ∀ i j, V i j ∈ E := fun i j => E.pow_mem (hdE j) _
  have hdet : V.det ≠ 0 := by
    have : V = (Matrix.vandermonde d).transpose := by
      ext i j; simp [hV, Matrix.vandermonde]
    rw [this, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hd
  have hx : x = V⁻¹.mulVec (V.mulVec x) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  have hinv : ∀ i j, V⁻¹ i j ∈ E := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    refine E.mul_mem (E.inv_mem (det_mem_subfield_of_entries_mem E V hVE)) ?_
    rw [Matrix.adjugate_apply]
    refine det_mem_subfield_of_entries_mem E _ fun a b => ?_
    by_cases hab : a = j
    · subst hab
      simp only [Matrix.updateRow_self]
      by_cases hbi : b = i
      · subst hbi; simp [E.one_mem]
      · simp [hbi, E.zero_mem]
    · rw [Matrix.updateRow_ne hab]; exact hVE a b
  have hy : ∀ b, V.mulVec x b ∈ E := by
    intro b
    have : V.mulVec x b = ∑ j, d j ^ (b : ℕ) * x j := by
      simp [hV, Matrix.mulVec, dotProduct]
    rw [this]; exact h b
  intro j
  rw [hx]
  show ∑ b, V⁻¹ j b * V.mulVec x b ∈ E
  exact E.sum_mem fun b _ => E.mul_mem (hinv j b) (hy b)

private theorem diag_entries_mem_of_trace_mem_of_regular_diag {Γ K : Type} [Group Γ] [Field K] (E : Subfield K) (r : Γ →* Matrix (Fin 4) (Fin 4) K)
    (g0 : Γ) (d : Fin 4 → K) (hD : r g0 = Matrix.diagonal d) (hd : Function.Injective d) (hdE : ∀ i, d i ∈ E)
    (htr : ∀ g, (r g).trace ∈ E) : ∀ x i, r x i i ∈ E := by
  intro x
  apply mem_subfield_of_vandermonde_sums_mem E d (fun i => r x i i) hd hdE
  intro b
  have h := htr (g0 ^ (b : ℕ) * x)
  rw [map_mul, map_pow, hD, Matrix.diagonal_pow] at h
  simpa [Matrix.trace, Matrix.diagonal_mul] using h

private theorem entry_products_mem_of_trace_mem_of_regular_diag {Γ K : Type} [Group Γ] [Field K] (E : Subfield K) (r : Γ →* Matrix (Fin 4) (Fin 4) K)
    (g0 : Γ) (d : Fin 4 → K) (hD : r g0 = Matrix.diagonal d) (hd : Function.Injective d) (hdE : ∀ i, d i ∈ E)
    (htr : ∀ g, (r g).trace ∈ E) : ∀ u y i, r u 0 i * r y i 0 ∈ E := by
  intro u y
  apply mem_subfield_of_vandermonde_sums_mem E d (fun i => r u 0 i * r y i 0) hd hdE
  intro b
  have h := diag_entries_mem_of_trace_mem_of_regular_diag E r g0 d hD hd hdE htr (u * g0 ^ (b : ℕ) * y) 0
  rw [map_mul, map_mul, map_pow, hD, Matrix.diagonal_pow, Matrix.mul_apply] at h
  convert h using 2 with i
  rw [Matrix.mul_diagonal]
  simp only [Pi.pow_apply]
  ring

private theorem triple_entry_products_mem_of_trace_regular_diag {Γ K : Type} [Group Γ] [Field K] (E : Subfield K) (r : Γ →* Matrix (Fin 4) (Fin 4) K)
    (g0 : Γ) (d : Fin 4 → K) (hD : r g0 = Matrix.diagonal d) (hd : Function.Injective d) (hdE : ∀ i, d i ∈ E)
    (htr : ∀ g, (r g).trace ∈ E) : ∀ u g w i j, r u 0 i * r g i j * r w j 0 ∈ E := by
  intro u g w i
  apply mem_subfield_of_vandermonde_sums_mem E d (fun j => r u 0 i * r g i j * r w j 0) hd hdE
  intro c
  have h := entry_products_mem_of_trace_mem_of_regular_diag E r g0 d hD hd hdE htr u (g * g0 ^ (c : ℕ) * w) i
  rw [map_mul, map_mul, map_pow, hD, Matrix.diagonal_pow, Matrix.mul_apply, Finset.mul_sum] at h
  convert h using 2 with j
  rw [Matrix.mul_diagonal]
  simp only [Pi.pow_apply]
  ring

private theorem exists_entry_ne_zero_of_irr {Γ K : Type} [Group Γ] [Field K] (r : Γ →* Matrix (Fin 4) (Fin 4) K)
    (hr : Irr r) : ∀ i j, ∃ g, r g i j ≠ 0 := by
  intro i j
  by_contra h
  push_neg at h
  let W : Submodule K (Matrix (Fin 4) (Fin 4) K) :=
    { carrier := {M | M i j = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Matrix.add_apply] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, Matrix.smul_apply, smul_eq_mul] at *
        rw [hx, mul_zero] }
  have hle : Submodule.span K (Set.range r) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact h g
  have hr' : Submodule.span K (Set.range r) = ⊤ := hr
  rw [hr'] at hle
  have hmem : (Matrix.of fun _ _ => (1 : K)) ∈ W := hle Submodule.mem_top
  have h1 : (1 : K) = 0 := hmem
  exact one_ne_zero h1

private theorem neg_entry_zero_two_eq_nu_mul_inv_entry_of_isGSp {Γ K : Type} [Group Γ] [Field K] (r : Γ →* Matrix (Fin 4) (Fin 4) K)
    (ν : Γ → K) (hG : ∀ g, IsGSp (ν g) (r g)) (g : Γ) : -(r g 0 2) = ν g * r g⁻¹ 1 3 := by
  have h1 : adj (r g) = ν g • r g⁻¹ := by
    have e : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc adj (r g) = adj (r g) * (r g * r g⁻¹) := by rw [e, mul_one]
      _ = (adj (r g) * r g) * r g⁻¹ := by rw [mul_assoc]
      _ = ν g • r g⁻¹ := by rw [hG g, smul_mul_assoc, one_mul]
  have h2 := congrFun (congrFun h1 1) 3
  simp [adj, sgn] at h2
  rw [← h2]

theorem UpperTheory.V.Ws.fibTorus :
    ∀ {Γ K : Type} [Group Γ] [Field K] (r : Γ →* M4 K) (ν : Γ → K) (g0 : Γ), (∀ g, IsGSp (ν g) (r g)) → (r g0).IsDiag →
          (∀ i j, i ≠ j → r g0 i i ≠ r g0 j j) → Irr r → ∃ s t : K, ∀ E : Subfield K, s ∈ E → t ∈ E → (∀ g, ν g ∈ E) → (∀ g, (r g).trace ∈ E) →
            (∀ i, r g0 i i ∈ E) → ∀ g i j, r g i j ∈ E := by
  intro Γ K _ _ r ν g0 hG hdiag hdist hirr
  choose gs hgs using exists_entry_ne_zero_of_irr r hirr
  refine ⟨r (gs 0 1) 0 1, r (gs 0 2) 0 2, fun E hs ht hν htr hdE => ?_⟩
  set d : Fin 4 → K := fun i => r g0 i i with hdd
  have hD : r g0 = Matrix.diagonal d := hdiag.diagonal_diag.symm
  have hd : Function.Injective d := by
    intro i j hij
    by_contra hne
    exact hdist i j hne hij
  have hT := triple_entry_products_mem_of_trace_regular_diag E r g0 d hD hd hdE htr
  have hS := entry_products_mem_of_trace_mem_of_regular_diag E r g0 d hD hd hdE htr
  have hx0 : r (gs 0 0) 0 0 ∈ E := diag_entries_mem_of_trace_mem_of_regular_diag E r g0 d hD hd hdE htr _ 0
  have hy : ∀ j, r (gs 0 j) 0 j ∈ E → r (gs j 0) j 0 ∈ E := by
    intro j hj
    have he := hS (gs 0 j) (gs j 0) j
    have : r (gs j 0) j 0 = r (gs 0 j) 0 j * r (gs j 0) j 0 / r (gs 0 j) 0 j := by
      field_simp [hgs 0 j]
    rw [this]
    exact E.div_mem he hj
  have hx3 : r (gs 0 3) 0 3 ∈ E := by
    set g2 := gs 0 2
    have hG2 := neg_entry_zero_two_eq_nu_mul_inv_entry_of_isGSp r ν hG g2
    have hne : r g2⁻¹ 1 3 ≠ 0 := by
      intro h0
      rw [h0, mul_zero, neg_eq_zero] at hG2
      exact hgs 0 2 hG2
    have hν0 : ν g2 ≠ 0 := by
      intro h0
      rw [h0, zero_mul, neg_eq_zero] at hG2
      exact hgs 0 2 hG2
    have hf := hT (gs 0 1) g2⁻¹ (gs 3 0) 1 3
    have he := hS (gs 0 3) (gs 3 0) 3
    have hinvE : r g2⁻¹ 1 3 ∈ E := by
      have : r g2⁻¹ 1 3 = -(r g2 0 2) / ν g2 := by rw [hG2]; field_simp
      rw [this]
      exact E.div_mem (E.neg_mem ht) (hν g2)
    have : r (gs 0 3) 0 3 = r (gs 0 1) 0 1 * r g2⁻¹ 1 3 * (r (gs 0 3) 0 3 * r (gs 3 0) 3 0) /
        (r (gs 0 1) 0 1 * r g2⁻¹ 1 3 * r (gs 3 0) 3 0) := by
      field_simp [hgs 0 1, hne, hgs 3 0]
    rw [this]
    exact E.div_mem (E.mul_mem (E.mul_mem hs hinvE) he) hf
  have hx : ∀ i, r (gs 0 i) 0 i ∈ E := by
    intro i
    fin_cases i
    · exact hx0
    · exact hs
    · exact ht
    · exact hx3
  intro g i j
  have h1 := hT (gs 0 i) g (gs j 0) i j
  have : r g i j = r (gs 0 i) 0 i * r g i j * r (gs j 0) j 0 / (r (gs 0 i) 0 i * r (gs j 0) j 0) := by
    field_simp [hgs 0 i, hgs j 0]
  rw [this]
  exact E.div_mem h1 (E.mul_mem (hx i) (hy j (hx j)))
