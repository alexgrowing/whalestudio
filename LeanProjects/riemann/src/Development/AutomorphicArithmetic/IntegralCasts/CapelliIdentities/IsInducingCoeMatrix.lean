import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qk27.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk27.inUJ :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) ↦
      g.conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g = UpperTheory.Reformulated.B.Qk27.Jm ε

theorem UpperTheory.Reformulated.B.Qk27.aux3 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
          g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g h hg hh
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk27.inUJ] at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem UpperTheory.Reformulated.B.Qk27.aux4 :
    ∀ {n : ℕ} (ε : Fin n → Bool),
      (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε *
          (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk27.Jm ε := by
  intro n ε
  rw [Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.Qk27.aux5 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g hg
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk27.inUJ] at hg ⊢
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv g
  generalize ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = b at h1 ⊢
  calc _ = b.conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g) * b := by rw [hg]
    _ = ((g : Matrix (Fin n) (Fin n) ℂ) * b).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε *
          ((g : Matrix (Fin n) (Fin n) ℂ) * b) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

noncomputable def UpperTheory.Reformulated.B.Qk27.UJ :
    {n : ℕ} → (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦
      { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk27.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)},
        mul_mem' := @UpperTheory.Reformulated.B.Qk27.aux3 n ε, one_mem' := UpperTheory.Reformulated.B.Qk27.aux4 ε,
        inv_mem' := @UpperTheory.Reformulated.B.Qk27.aux5 n ε : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ }

noncomputable def UpperTheory.Reformulated.B.Qk27.coeMatrixAlt :
    {n : ℕ} → (ε : Fin n → Bool) → ↥(UpperTheory.Reformulated.B.Qk27.UJ ε) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : ↥(UpperTheory.Reformulated.B.Qk27.UJ ε)) ↦
      (↑(↑g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

private theorem UpperTheory.Reformulated.B.Qk27.Jm_mul_self {n : ℕ} (ε : Fin n → Bool) :
    UpperTheory.Reformulated.B.Qk27.Jm ε * UpperTheory.Reformulated.B.Qk27.Jm ε = 1 := by
  unfold UpperTheory.Reformulated.B.Qk27.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem UpperTheory.Reformulated.B.Qk27.isInducing_coeMatrix :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsInducing (UpperTheory.Reformulated.B.Qk27.coeMatrixAlt ε) := by
  intro n ε
  let k : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun x ↦ (x, MulOpposite.op (UpperTheory.Reformulated.B.Qk27.Jm ε * (x.conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε)))
  have hk : Continuous k :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      (continuous_const.matrix_mul (continuous_id.matrix_conjTranspose.matrix_mul continuous_const)))
  have hc : Continuous (UpperTheory.Reformulated.B.Qk27.coeMatrixAlt ε) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : k ∘ UpperTheory.Reformulated.B.Qk27.coeMatrixAlt ε =
      Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘
        (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk27.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    funext g
    have hg : (g.1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε * g.1 =
        UpperTheory.Reformulated.B.Qk27.Jm ε := g.2
    have hi : ((g.1⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk27.Jm ε *
          ((g.1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk27.Jm ε) := by
      apply Units.inv_eq_of_mul_eq_one_left
      rw [Matrix.mul_assoc, hg, UpperTheory.Reformulated.B.Qk27.Jm_mul_self]
    exact Prod.ext rfl (congrArg MulOpposite.op hi.symm)
  refine Topology.IsInducing.of_comp hc hk ?_
  rw [he]
  exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
