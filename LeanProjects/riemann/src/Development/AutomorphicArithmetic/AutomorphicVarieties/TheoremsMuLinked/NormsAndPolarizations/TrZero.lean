import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.trZero_inner {K : Type} [Field K] {n : ℕ}
    (D : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K)
    (hD : ∀ A B, D (A * B) = D A * B + A * D B) : ∃ Y, ∀ A, D A = A * Y - Y * A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun A => Subsingleton.elim _ _⟩
  let o : Fin n := ⟨0, hn⟩
  refine ⟨-∑ i, D (single i o 1) * single o i 1, fun A => ?_⟩
  have h1 : ∀ i, A * single i o (1 : K) = ∑ j, A j i • single j o (1 : K) := by
    intro i
    ext a b
    by_cases hb : o = b
    · subst hb
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, hb, Matrix.mul_apply]
  have h2 : ∀ j, single o j (1 : K) * A = ∑ i, A j i • single o i (1 : K) := by
    intro j
    ext a b
    by_cases ha : o = a
    · subst ha
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, ha, Matrix.mul_apply]
  have h3 : ∑ i, single i o (1 : K) * single o i (1 : K) = (1 : Matrix (Fin n) (Fin n) K) := by
    simp only [Matrix.single_mul_single_same, mul_one]
    exact Matrix.sum_single_one
  have h4 : A * ∑ i, D (single i o 1) * single o i 1
      = (∑ i, D (single i o 1) * single o i 1) * A - D A := by
    have e1 : ∀ i, A * (D (single i o 1) * single o i (1 : K))
        = D (A * single i o 1) * single o i 1 - D A * (single i o 1 * single o i 1) := by
      intro i
      rw [hD]; noncomm_ring
    rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_sub_distrib,
      ← Finset.mul_sum, h3, mul_one, Finset.sum_mul]
    congr 1
    simp only [h1, map_sum, map_smul, Finset.sum_mul, mul_assoc, h2, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  rw [mul_neg, neg_mul, h4]; abel

theorem UpperTheory.V.Th.Nm.trZero :
    ∀ {K G : Type} [Field K] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) K) (z : G → Matrix (Fin n) (Fin n) K), Submodule.span K (Set.range (mat ρ)) = ⊤ → (∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) → (∀ g, (z g * mat ρ g).trace = 0) → ∃ Y, ∀ g, z g = mat ρ g * Y * mat ρ g⁻¹ - Y := by
  intro K G _ _ n ρ z hsp hc ht
  have hmul : ∀ g h, mat ρ (g * h) = mat ρ g * mat ρ h := by
    intro g h; simp [mat]
  have hone : mat ρ 1 = 1 := by simp [mat]
  have hinv : ∀ g, mat ρ g⁻¹ * mat ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, hone]
  have hinv' : ∀ g, mat ρ g * mat ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, hone]
  let d : G → Matrix (Fin n) (Fin n) K := fun g => z g * mat ρ g
  have hd : ∀ g h, d (g * h) = d g * mat ρ h + mat ρ g * d h := by
    intro g h
    simp only [d]
    rw [hc, hmul, add_mul, mul_assoc (mat ρ g * z h), ← mul_assoc (mat ρ g⁻¹), hinv, one_mul]
    simp only [mul_assoc]
  let R := Finsupp.linearCombination K (mat ρ)
  let E := Finsupp.linearCombination K d
  have hR : LinearMap.range R = ⊤ := by rw [Finsupp.range_linearCombination]; exact hsp
  have hker : ∀ y, R y = 0 → E y = 0 := by
    intro y hy
    have key : ∀ h, ∀ y : G →₀ K, (d h * R y).trace + (mat ρ h * E y).trace = 0 := by
      intro h y
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        simp only [map_add, mul_add, trace_add]
        linear_combination ha + hb
      | single g a =>
        have := ht (h * g)
        change (d (h * g)).trace = 0 at this
        rw [hd, trace_add] at this
        simp only [R, E, Finsupp.linearCombination_single, mul_smul_comm, trace_smul, smul_eq_mul]
        rw [← mul_add, this, mul_zero]
    have k2 : ∀ A : Matrix (Fin n) (Fin n) K, (A * E y).trace = 0 := by
      intro A
      have hA : A ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        simpa [hy] using key h y
      | zero => simp
      | add a b _ _ ha hb => simp [add_mul, ha, hb]
      | smul a b _ hb => simp [hb]
    ext i j
    simpa [Matrix.trace_single_mul] using k2 (single j i 1)
  obtain ⟨s, hs⟩ := R.exists_rightInverse_of_surjective hR
  let D := E ∘ₗ s
  have hDg : ∀ g, D (mat ρ g) = d g := by
    intro g
    have h0 : R (s (mat ρ g) - Finsupp.single g 1) = 0 := by
      have := LinearMap.congr_fun hs (mat ρ g)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [map_sub, this]; simp [R]
    have := hker _ h0
    rw [map_sub, sub_eq_zero] at this
    simpa [D, E] using this
  have hD : ∀ A B, D (A * B) = D A * B + A * D B := by
    intro A B
    have hA : A ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
    have hB : B ∈ Submodule.span K (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hB using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [← hmul, hDg, hDg, hDg, hd]
      | zero => simp
      | add a b _ _ ha hb => simp only [mul_add, map_add, ha, hb]; abel
      | smul a b _ hb => simp only [mul_smul_comm, map_smul, hb, smul_add]
    | zero => simp
    | add a b _ _ ha hb => simp only [add_mul, map_add, ha, hb]; abel
    | smul a b _ hb => simp only [smul_mul_assoc, map_smul, hb, smul_add]
  obtain ⟨Y, hY⟩ := UpperTheory.V.Th.Nm.trZero_inner D hD
  refine ⟨Y, fun g => ?_⟩
  have h1 := hY (mat ρ g)
  rw [hDg] at h1
  have h2 : z g = d g * mat ρ g⁻¹ := by simp only [d]; rw [mul_assoc, hinv', mul_one]
  rw [h2, h1, sub_mul, mul_assoc Y, hinv', mul_one]
