import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup

open Matrix

namespace GlobalTheory.CompanionTheory.Flag

theorem exists_frame_extension {n D : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (h1 : Cᴴ * C = 1)
    (U : Submodule ℂ (Fin n → ℂ)) (hU : ∀ v, C *ᵥ v ∈ U) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℂ), Bᴴ * B = 1 ∧ Cᴴ * B = 0 ∧
      ∀ y, y ∈ U ↔ ∃ u w, y = C *ᵥ u + B *ᵥ w := by
  classical
  let W' : Submodule ℂ (Fin n → ℂ) := U ⊓ LinearMap.ker (Matrix.mulVecLin Cᴴ)
  obtain ⟨r, B, hB1, hBW⟩ := GlobalTheory.IsoTorus.exists_frame W'
  have hmemW' : ∀ y, y ∈ W' ↔ y ∈ U ∧ Cᴴ *ᵥ y = 0 := fun y => by
    simp [W', Submodule.mem_inf]
  have hBin : ∀ w, B *ᵥ w ∈ W' := fun w => (hBW _).mpr (by
    rw [Matrix.mulVec_mulVec w (B * Bᴴ) B, Matrix.mul_assoc, hB1, Matrix.mul_one])
  have hCB : Cᴴ * B = 0 := by
    ext i j
    have h := congrFun ((hmemW' _).mp (hBin (Pi.single j 1))).2 i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    simpa using h
  refine ⟨r, B, hB1, hCB, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨z, hzdef⟩ : ∃ z, z = y - C *ᵥ (Cᴴ *ᵥ y) := ⟨_, rfl⟩
    have hCC : Cᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ y)) = Cᴴ *ᵥ y := by
      rw [Matrix.mulVec_mulVec (Cᴴ *ᵥ y) Cᴴ C, h1, Matrix.one_mulVec]
    have hz : z ∈ W' := (hmemW' z).mpr ⟨hzdef ▸ U.sub_mem hy (hU _), by
      rw [hzdef, Matrix.mulVec_sub, hCC, sub_self]⟩
    have hz' := (hBW z).mp hz
    refine ⟨Cᴴ *ᵥ y, Bᴴ *ᵥ z, ?_⟩
    rw [Matrix.mulVec_mulVec z B Bᴴ, hz', hzdef]
    abel
  · rintro ⟨u, w, rfl⟩
    exact U.add_mem (hU u) ((hmemW' _).mp (hBin w)).1

private theorem append_cols_mulVec_eq_add {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (v : Fin (D + r) → ℂ) :
    (Matrix.of fun i => Fin.append (C i) (B i)) *ᵥ v =
      C *ᵥ (fun j => v (Fin.castAdd r j)) + B *ᵥ (fun j => v (Fin.natAdd D j)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

private theorem append_cols_conjTranspose_mul_eq_one {n D r : ℕ} (C : Matrix (Fin n) (Fin D) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (h1 : Cᴴ * C = 1) (h2 : Bᴴ * B = 1) (h3 : Cᴴ * B = 0) :
    (Matrix.of fun i => Fin.append (C i) (B i))ᴴ * (Matrix.of fun i => Fin.append (C i) (B i)) = 1 := by
  have h4 : Bᴴ * C = 0 := by simpa using congrArg Matrix.conjTranspose h3
  ext c c'
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c <;> refine Fin.addCases (fun j' => ?_) (fun j' => ?_) c'
  · have h := congrFun (congrFun h1 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  · have hne : Fin.castAdd r j ≠ Fin.natAdd D j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h3 j) j'
    simpa [Matrix.mul_apply] using h
  · have hne : Fin.natAdd D j ≠ Fin.castAdd r j' := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    rw [Matrix.one_apply_ne hne]
    have h := congrFun (congrFun h4 j) j'
    simpa [Matrix.mul_apply] using h
  · have h := congrFun (congrFun h2 j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem exists_flag_frame : ∀ {n a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    Monotone W → ∃ (D : ℕ) (C : Matrix (Fin n) (Fin D) ℂ) (τ : Fin D → ℕ), Cᴴ * C = 1 ∧
      Monotone τ ∧ (∀ c, τ c < a) ∧ ∀ (i : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W i ↔ ∃ v : Fin D → ℂ, y = C *ᵥ v ∧ ∀ c, (i : ℕ) ≤ τ c → v c = 0 := by
  intro n a
  induction a with
  | zero =>
    intro W hW0 _
    refine ⟨0, 0, fun _ => 0, ?_, fun x _ _ => x.elim0, fun c => c.elim0, fun i y => ?_⟩
    · ext i j
      exact i.elim0
    · have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi
      rw [hW0, Submodule.mem_bot]
      constructor
      · rintro rfl
        exact ⟨0, by simp, fun c => c.elim0⟩
      · rintro ⟨v, rfl, -⟩
        simp
  | succ a ih =>
    intro W hW0 hWm
    obtain ⟨D, C, τ, hC1, hτm, hτa, hCW⟩ := ih (fun i => W i.castSucc) (by simpa using hW0)
      (fun i j hij => hWm (Fin.castSucc_le_castSucc_iff.mpr hij))
    have hU : ∀ v, C *ᵥ v ∈ W (Fin.last (a + 1)) := fun v =>
      hWm (Fin.castSucc_lt_last (Fin.last a)).le
        ((hCW (Fin.last a) _).mpr ⟨v, rfl, fun c h => absurd h (not_le.mpr (hτa c))⟩)
    obtain ⟨r, B, hB1, hCB, hBU⟩ := exists_frame_extension C hC1 (W (Fin.last (a + 1))) hU
    refine ⟨D + r, Matrix.of fun i => Fin.append (C i) (B i), Fin.append τ (fun _ => a),
      append_cols_conjTranspose_mul_eq_one C B hC1 hB1 hCB, ?_, ?_, ?_⟩
    · intro c c' hcc'
      induction c using Fin.addCases with
      | left j =>
        induction c' using Fin.addCases with
        | left j' =>
          simp only [Fin.append_left]
          exact hτm (Fin.le_iff_val_le_val.mpr (by simpa using Fin.le_iff_val_le_val.mp hcc'))
        | right j' =>
          simp only [Fin.append_left, Fin.append_right]
          exact (hτa j).le
      | right j =>
        induction c' using Fin.addCases with
        | left j' =>
          exfalso
          have h := Fin.le_iff_val_le_val.mp hcc'
          have := j'.isLt
          simp at h
          omega
        | right j' =>
          simp only [Fin.append_right]
          exact le_refl _
    · intro c
      refine Fin.addCases (fun j => ?_) (fun j => ?_) c
      · simp only [Fin.append_left]
        exact (hτa j).trans (Nat.lt_succ_self a)
      · simp only [Fin.append_right]
        exact Nat.lt_succ_self a
    · intro i y
      induction i using Fin.lastCases with
      | last =>
        rw [hBU]
        constructor
        · rintro ⟨u, w, rfl⟩
          refine ⟨Fin.append u w, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp
          · exfalso
            revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro h
              simp only [Fin.append_left, Fin.val_last] at h
              have := hτa j
              omega
            · intro h
              simp only [Fin.append_right, Fin.val_last] at h
              omega
        · rintro ⟨v, rfl, -⟩
          exact ⟨_, _, append_cols_mulVec_eq_add C B v⟩
      | cast i' =>
        refine (hCW i' y).trans ?_
        constructor
        · rintro ⟨v, rfl, hv⟩
          refine ⟨Fin.append v 0, ?_, fun c hc => ?_⟩
          · rw [append_cols_mulVec_eq_add]
            simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
            rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, Matrix.mulVec_zero, add_zero]
          · revert hc
            refine Fin.addCases (fun j => ?_) (fun j => ?_) c
            · intro hc
              simp only [Fin.append_left, Fin.val_castSucc] at hc ⊢
              exact hv j hc
            · intro _
              simp
        · rintro ⟨v, rfl, hv⟩
          refine ⟨fun j => v (Fin.castAdd r j), ?_, fun c hc => hv (Fin.castAdd r c) (by simpa using hc)⟩
          rw [append_cols_mulVec_eq_add]
          have hz : (fun j => v (Fin.natAdd D j)) = 0 := funext fun j => hv _ (by
            have := i'.isLt
            simp only [Fin.append_right, Fin.val_castSucc]
            omega)
          rw [hz, Matrix.mulVec_zero, add_zero]

end GlobalTheory.CompanionTheory.Flag
