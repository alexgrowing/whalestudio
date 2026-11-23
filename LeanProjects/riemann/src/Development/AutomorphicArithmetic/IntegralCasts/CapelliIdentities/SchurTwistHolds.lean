import Mathlib

noncomputable def UpperTheory.Reformulated.B.H13.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.H13.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.H13.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.H13.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.H13.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.H13.aux5 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (1 : Γ)) *
          (r : Γ → GL (Fin n) k) (1 : Γ) =
        (1 : GL (Fin n) k) := by
  intro Γ k _ _ n r χ
  simp

theorem UpperTheory.Reformulated.B.H13.aux6 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s t : Γ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (s * t)) *
          (r : Γ → GL (Fin n) k) (s * t) =
        (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s *
          ((Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) t) * (r : Γ → GL (Fin n) k) t) := by
  intro Γ k _ _ n r χ s t
  have hc : ∀ (c : kˣ) (A : GL (Fin n) k),
      A * Matrix.GeneralLinearGroup.scalar (Fin n) c = Matrix.GeneralLinearGroup.scalar (Fin n) c * A := by
    intro c A
    apply Units.ext
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute (c : k) (fun x => Commute.all _ _) (A : Matrix (Fin n) (Fin n) k)).eq.symm
  rw [map_mul, map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (r s), hc, mul_assoc]

noncomputable def UpperTheory.Reformulated.B.H13.tw :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* kˣ) → Γ →* GL (Fin n) k :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) ↦
      {
        toFun := fun (s : Γ) ↦
          (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s,
        map_one' := UpperTheory.Reformulated.B.H13.aux5 r χ, map_mul' := UpperTheory.Reformulated.B.H13.aux6 r χ : Γ →* GL (Fin n) k }

noncomputable def UpperTheory.Reformulated.B.H13.SchurTw :
    Prop :=
    ∀ (Γ Γ' k : Type) [inst : Group Γ] [inst_1 : Group Γ'] [inst_2 : Field k] [IsAlgClosed k] (n : ℕ)
      (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
      UpperTheory.Reformulated.B.H13.IsIrr (r.comp φ) →
        δ.comp φ = (1 : Γ' →* kˣ) → UpperTheory.Reformulated.B.H13.RepIso r (UpperTheory.Reformulated.B.H13.tw r δ) → δ = (1 : Γ →* kˣ)

theorem UpperTheory.Reformulated.B.H13.schur_twist_holds :
    UpperTheory.Reformulated.B.H13.SchurTw := by
  intro Γ Γ' k _ _ _ _ n r φ δ hirr hδ hiso
  obtain ⟨hne, -, hmin⟩ := hirr
  obtain ⟨g, hg⟩ := hiso
  have hg' : ∀ s : Γ, Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s * g = g * r s := by
    intro s
    have h : Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s = g * r s * g⁻¹ := hg s
    rw [h, inv_mul_cancel_right]
  have hcomm : ∀ t : Γ', r (φ t) * g = g * r (φ t) := by
    intro t
    have h1 : δ (φ t) = 1 := DFunLike.congr_fun hδ t
    have h := hg' (φ t)
    rwa [h1, map_one, one_mul] at h
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v : Fin n → k,
      v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c ↔
        (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have htop : Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c = ⊤ := by
    refine (hmin _ le_top ?_).resolve_left hc
    intro t v hv
    rw [hmem] at hv ⊢
    have h : (r (φ t) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k)
        = (g : Matrix (Fin n) (Fin n) k) * (r (φ t) : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    change (g : Matrix (Fin n) (Fin n) k).mulVec ((r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v)
      = c • (r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hgv : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [← hmem, htop]
    exact Submodule.mem_top
  have hcent : ∀ A : GL (Fin n) k, g * A = A * g := by
    intro A
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgv, hgv, Matrix.mulVec_smul]
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton (Fin n → k) inferInstance
  obtain ⟨i⟩ := hn
  refine MonoidHom.ext fun s => ?_
  have h := hg' s
  rw [hcent, mul_left_inj, mul_eq_right] at h
  have h2 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) i i) h
  apply Units.ext
  simpa using h2
