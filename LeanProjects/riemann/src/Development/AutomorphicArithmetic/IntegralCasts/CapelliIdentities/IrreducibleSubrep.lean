import Mathlib

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.IrreducibleSubrep.irr_of_iso :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k},
      UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r → UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso r r' → UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r' := by
  intro Γ k _ _ n r r' hr hiso
  obtain ⟨hne, -, hmin⟩ := hr
  obtain ⟨g, hg⟩ := hiso
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => ?_⟩
  have hcomm : ∀ s : Γ, (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
      = (r' s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul, hg s, inv_mul_cancel_right]
  have hsec : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec
      (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv r
      (W'.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) := by
    intro s v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    exact hW' s _ hv
  rcases hmin _ le_top hinv with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w) (by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec]; exact hw)
    rw [← hsec w, h0, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec] at h0
