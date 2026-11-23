import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents {C K : Type} [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (hn : n = 2 ∨ n = 3) (A : Subalgebra C (Matrix (Fin n) (Fin n) K)) (h2 : IsUnit (2 : C))
    (hY : Matrix.diagonal (fun i => (w n i : K)) ∈ A) (i : Fin n) : Matrix.single i i (1 : K) ∈ A := by
  have key : ∀ M : Matrix (Fin n) (Fin n) K, (2 : C) • M ∈ A → M ∈ A := by
    intro M hM
    have := A.smul_mem hM (↑h2.unit⁻¹ : C)
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  have hYY := A.mul_mem hY hY
  rcases hn with rfl | rfl
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 2) 0 (1 : K) = 1 + Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.add_mem A.one_mem hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 2) 1 (1 : K) = 1 - Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem A.one_mem hY
      rw [← e] at h
      exact h
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 3) 0 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) +
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.add_mem hYY hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 3) 1 (1 : K) =
          (2 : C) • (1 - Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K))) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.smul_mem (A.sub_mem A.one_mem hYY) (2 : C)
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (2 : Fin 3) 2 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) -
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem hYY hY
      rw [← e] at h
      exact h

theorem UpperTheory.V.Fr.idem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F n K), Integral O C ρ → ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range ρ.r) := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ ρ hI i
  haveI : CharP (ResidueField O) l := IsCoef.char
  have hunit : ∀ x : C, res O C x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra h
    exact hx ((res_eq_zero_iff O C x).2 ((IsLocalRing.mem_maximalIdeal x).2 h))
  have h2 : IsUnit (2 : C) := by
    apply hunit
    rw [map_ofNat]
    intro h0
    have h0' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h0'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).1 h0')
  obtain ⟨ζ, hζr, hζ⟩ := hI.ze
  have hζu : IsUnit ζ := by
    apply hunit
    rw [hζr]
    intro h0
    apply hF.baseSubgroup_spec
    rw [sub_eq_zero] at h0
    try simp only [← Units.val_inv_eq_inv_val] at h0
    have hx : F.Ψ ↑F.g0 = (F.Ψ ↑F.g0)⁻¹ := Units.ext h0
    calc F.Ψ ↑F.g0 ^ 2 = F.Ψ ↑F.g0 * F.Ψ ↑F.g0 := sq _
      _ = F.Ψ ↑F.g0 * (F.Ψ ↑F.g0)⁻¹ := by rw [← hx]
      _ = 1 := mul_inv_cancel _
  have hD : ρ.r F.g0 - ρ.r (F.star F.g0) = ζ • Matrix.diagonal (fun i => (w n i : K)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, Algebra.smul_def, hζ a]
      ring
    · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab, smul_zero]
      exact ρ.diag a b hab
  have hspan : (Algebra.adjoin C (Set.range ρ.r)).toSubmodule = Submodule.span C (Set.range ρ.r) := by
    rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq]
  have hmem : ρ.r F.g0 - ρ.r (F.star F.g0) ∈ Submodule.span C (Set.range ρ.r) :=
    Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hY : Matrix.diagonal (fun i => (w n i : K)) ∈ Algebra.adjoin C (Set.range ρ.r) := by
    rw [← Subalgebra.mem_toSubmodule, hspan]
    have h := Submodule.smul_mem _ (↑hζu.unit⁻¹ : C) hmem
    rwa [hD, smul_smul, IsUnit.val_inv_mul, one_smul] at h
  rw [← hspan, Subalgebra.mem_toSubmodule]
  exact UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents hn _ h2 hY i
