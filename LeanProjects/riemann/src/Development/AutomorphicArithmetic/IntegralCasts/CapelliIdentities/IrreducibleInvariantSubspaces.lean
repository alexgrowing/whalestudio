import Mathlib

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.irr_conj :
    ∀ {k : Type} [inst : Field k] {Γ : Type} [inst_1 : Group Γ] {n : ℕ} (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k),
      (∀ (x : Γ), (r' : Γ → GL (Fin n) k) x = g * (r : Γ → GL (Fin n) k) x * g⁻¹) →
        UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r' → UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r := by
  intro k _ Γ _ n r r' g h hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  have hgg : ∀ v : Fin n → k, (↑(g⁻¹) : Matrix (Fin n) (Fin n) k).mulVec
      ((↑g : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv r'
      (W.comap (Matrix.mulVecLin (↑(g⁻¹) : Matrix (Fin n) (Fin n) k))) := by
    intro x v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [h x, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgg]
    exact hW x _ hv
  rcases hmin _ le_top hinv with h0 | h1
  · left
    rw [Submodule.eq_bot_iff] at h0 ⊢
    intro v hv
    have h2 : (↑g : Matrix (Fin n) (Fin n) k).mulVec v = 0 := by
      apply h0
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg]
      exact hv
    rw [← hgg v, h2, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h1 ⊢
    intro v
    have h2 := h1 ((↑g : Matrix (Fin n) (Fin n) k).mulVec v)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg] at h2
