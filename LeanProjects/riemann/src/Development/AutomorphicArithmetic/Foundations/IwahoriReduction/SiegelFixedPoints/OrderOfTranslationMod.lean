import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSLMapMulInvMem

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem exists_finite_residue_reps_mod_natCast (M K : ℕ) (hK : K ∣ M) (L γ : SL(2, ℤ))
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) L =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ) (i j : Fin 2) :
    ((L i j : ℤ) : ZMod K) = ((γ i j : ℤ) : ZMod K) := by
  have h1 : ((L i j : ℤ) : ZMod M) = ((γ i j : ℤ) : ZMod M) :=
    congrArg (fun g : SL(2, ZMod M) => g i j) h
  have h2 := congrArg (ZMod.castHom hK (ZMod K)) h1
  simpa only [map_intCast] using h2

private theorem exists_mem_mul_or_neg_mul_symm (M : ℕ) (a b : ℕ) : Tm M (a + b) = Tm M a * Tm M b := by
  simp only [Tm, pow_add, map_mul]

private theorem tm_apply_eq_cast_upper_unipotent (M k : ℕ) (i j : Fin 2) :
    (Tm M k) i j = (((!![1, (k : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M) := by
  rw [← ModularGroup.coe_T_zpow, zpow_natCast]
  rfl

private theorem exists_mem_mul_or_neg_mul_trans (M : ℕ) (j : ℕ) : Tm M (M * j) = 1 := by
  ext i k
  rw [tm_apply_eq_cast_upper_unipotent]
  fin_cases i <;> fin_cases k <;> simp

private theorem tm_mod_eq (M : ℕ) (k : ℕ) : Tm M (k % M) = Tm M k := by
  conv_rhs => rw [← Nat.mod_add_div k M]
  rw [exists_mem_mul_or_neg_mul_symm, exists_mem_mul_or_neg_mul_trans, mul_one]

private theorem eq_of_tm_eq_of_lt (M : ℕ) (a b : ℕ) (ha : a < M) (hb : b < M) (h : Tm M a = Tm M b) : a = b := by
  have h1 := congrArg (fun g : SL(2, ZMod M) => g 0 1) h
  simp only [tm_apply_eq_cast_upper_unipotent] at h1
  simp at h1
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

private theorem tm_mem_map_gam (N l M : ℕ) (k : ℕ) :
    Tm M k ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
  refine Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ ?_ k)
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T]

private theorem liftSL_mem_gam_and_map_eq_of_mem_gs (N l M : ℕ) [NeZero M] (hM : N * l ∣ M) (γ : SL(2, ZMod M)) (hγ : γ ∈ Gs N l M) :
    liftSL M γ ∈ Gam N l ∧ Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ := by
  have hγ' : γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
    simpa [Gs] using hγ
  obtain ⟨γ', hg', rfl⟩ := Subgroup.mem_map.1 hγ'
  have hL : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ')) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' :=
    Classical.epsilon_spec (p := fun g => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ') ⟨γ', rfl⟩
  refine ⟨?_, hL⟩
  have eN := exists_finite_residue_reps_mod_natCast M N (dvd_trans (dvd_mul_right N l) hM) _ _ hL
  have el := exists_finite_residue_reps_mod_natCast M l (dvd_trans (dvd_mul_left l N) hM) _ _ hL
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hg'
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem] at h1 ⊢
    rw [eN, eN, eN]
    exact h1
  · rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [el]
    exact h0

theorem UpperTheory.Kd.L.reps :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (M : ℕ) [NeZero M], N * l ∣ M → (∃ R, IsReps N l M R) ∧ ∀ γ ∈ Gs N l M, ∀ r₀, Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ ∧ gm r₀ * liftSL M γ ∈ CongruenceSubgroup.Gamma0 N ∧ ((en (gm r₀ * liftSL M γ) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL M γ) 0 0 ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL M γ) 1 0 := by
  intro l _ N _ c d gm hP M _ hM
  classical
  refine ⟨?_, ?_⟩
  · let orb : SL(2, ZMod M) → Set (SL(2, ZMod M)) := fun γ => Set.range (fun k : ℕ => γ * Tm M k)
    let rep : SL(2, ZMod M) → SL(2, ZMod M) := fun γ => Classical.epsilon (fun x => x ∈ orb γ)
    have h0 : Tm M 0 = 1 := by simpa using exists_mem_mul_or_neg_mul_trans M 0
    have self_mem : ∀ γ, γ ∈ orb γ := fun γ => ⟨0, show γ * Tm M 0 = γ by rw [h0, mul_one]⟩
    have rep_mem : ∀ γ, rep γ ∈ orb γ := fun γ => Classical.epsilon_spec ⟨γ, self_mem γ⟩
    have orb_eq : ∀ γ x, x ∈ orb γ → orb x = orb γ := by
      rintro γ _ ⟨j, rfl⟩
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨j + k, show γ * Tm M (j + k) = γ * Tm M j * Tm M k by rw [mul_assoc, ← exists_mem_mul_or_neg_mul_symm]⟩
      · rintro ⟨k, rfl⟩
        refine ⟨k + (M - 1) * j, ?_⟩
        have hM1 : j + (k + (M - 1) * j) = k + M * j := by
          have : 1 ≤ M := NeZero.one_le
          obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        show γ * Tm M j * Tm M (k + (M - 1) * j) = γ * Tm M k
        rw [mul_assoc, ← exists_mem_mul_or_neg_mul_symm, hM1, exists_mem_mul_or_neg_mul_symm, exists_mem_mul_or_neg_mul_trans, mul_one]
    have rep_eq : ∀ γ x, x ∈ orb γ → rep x = rep γ := by
      intro γ x hx
      simp only [rep]
      rw [orb_eq γ x hx]
    have hGs : ∀ γ, γ ∈ Gs N l M ↔ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
      intro γ
      simp [Gs]
    refine ⟨(Gs N l M).image rep, ?_, ?_⟩
    · intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, hj⟩ := rep_mem γ
      rw [← hj, hGs]
      exact Subgroup.mul_mem _ ((hGs γ).1 hγ) (tm_mem_map_gam N l M j)
    · intro γ hγ
      have hin : γ ∈ orb (rep γ) := by
        rw [orb_eq γ (rep γ) (rep_mem γ)]
        exact self_mem γ
      obtain ⟨k, hk⟩ := hin
      have hk : rep γ * Tm M k = γ := hk
      refine ⟨(rep γ, k % M), ⟨Finset.mem_image_of_mem _ hγ, Nat.mod_lt _ (NeZero.pos M), ?_⟩, ?_⟩
      · show γ = rep γ * Tm M (k % M)
        rw [tm_mod_eq, hk]
      · rintro ⟨r, k'⟩ ⟨hr, hk', hγr⟩
        dsimp only at hr hk' hγr
        obtain ⟨γ1, -, rfl⟩ := Finset.mem_image.1 hr
        have hin1 : γ ∈ orb γ1 := by
          rw [← orb_eq γ1 (rep γ1) (rep_mem γ1)]
          exact ⟨k', hγr.symm⟩
        have hr1 : rep γ = rep γ1 := rep_eq γ1 γ hin1
        have hT : Tm M k' = Tm M (k % M) := by
          have e : rep γ1 * Tm M k' = rep γ1 * Tm M (k % M) := by
            rw [← hγr, tm_mod_eq, ← hr1, hk]
          exact mul_left_cancel e
        have := eq_of_tm_eq_of_lt M k' (k % M) hk' (Nat.mod_lt _ (NeZero.pos M)) hT
        simp only [Prod.mk.injEq]
        exact ⟨hr1.symm, this⟩
  · intro γ hγ r₀
    obtain ⟨hLG, hL⟩ := liftSL_mem_gam_and_map_eq_of_mem_gs N l M hM γ hγ
    obtain ⟨hL1, hL0⟩ := Subgroup.mem_inf.1 hLG
    rw [CongruenceSubgroup.Gamma1_mem] at hL1
    rw [CongruenceSubgroup.Gamma0_mem] at hL0
    have detL : (((liftSL M γ) 0 0 : ℤ) : ZMod l) * (((liftSL M γ) 1 1 : ℤ) : ZMod l) = 1 := by
      have h1 := (liftSL M γ).2
      rw [Matrix.det_fin_two] at h1
      have h2 := congrArg (Int.cast : ℤ → ZMod l) h1
      push_cast at h2
      rw [hL0, mul_zero, sub_zero] at h2
      exact h2
    have hL00 : (((liftSL M γ) 0 0 : ℤ) : ZMod l) ≠ 0 := left_ne_zero_of_mul_eq_one detL
    have hg00 : (((gm r₀) 0 0 : ℤ) : ZMod l) ≠ 0 := by
      intro h0
      have hc := hP.col r₀
      rw [h0, mul_zero] at hc
      have h1 := (gm r₀).2
      rw [Matrix.det_fin_two] at h1
      have h2 := congrArg (Int.cast : ℤ → ZMod l) h1
      push_cast at h2
      rw [h0, hc] at h2
      simp at h2
    refine ⟨hL, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (hP.g0 r₀) (by rw [CongruenceSubgroup.Gamma0_mem]; exact hL1.2.2)
    · have ga := hP.ga r₀
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at ga ⊢
      push_cast
      rw [hL1.1, hL1.2.2, mul_one, mul_zero, add_zero]
      exact ga
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL0, mul_zero, add_zero]
      exact mul_ne_zero hg00 hL00
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL0, mul_zero, add_zero, hP.col r₀]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r₀.ne_zero) hg00) hL00
