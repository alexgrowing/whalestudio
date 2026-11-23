import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qk16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk16.inUJ :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) ↦
      g.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * g = UpperTheory.Reformulated.B.Qk16.Jm ε

theorem UpperTheory.Reformulated.B.Qk16.aux3 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
          g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g h hg hh
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * ((g : Matrix (Fin n) (Fin n) ℂ) * (h : Matrix (Fin n) (Fin n) ℂ))
      = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        UpperTheory.Reformulated.B.Qk16.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)) * (h : Matrix (Fin n) (Fin n) ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [hg, hh]

theorem UpperTheory.Reformulated.B.Qk16.aux4 :
    ∀ {n : ℕ} (ε : Fin n → Bool),
      (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε *
          (↑(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        UpperTheory.Reformulated.B.Qk16.Jm ε := by
  intro n ε
  simp

theorem UpperTheory.Reformulated.B.Qk16.aux5 :
    ∀ {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
      g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} →
        g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)} := by
  intro n ε g hg
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Qk16.inUJ] at hg ⊢
  have h1 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv g
  generalize ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = B at h1 ⊢
  generalize (g : Matrix (Fin n) (Fin n) ℂ) = A at h1 hg
  calc B.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * B
      = B.conjTranspose * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) * B := by rw [hg]
    _ = (A * B).conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * (A * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Qk16.Jm ε := by rw [h1]; simp

noncomputable def UpperTheory.Reformulated.B.Qk16.UJ :
    {n : ℕ} → (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦
      { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | UpperTheory.Reformulated.B.Qk16.inUJ ε (↑g : Matrix (Fin n) (Fin n) ℂ)},
        mul_mem' := @UpperTheory.Reformulated.B.Qk16.aux3 n ε, one_mem' := UpperTheory.Reformulated.B.Qk16.aux4 ε,
        inv_mem' := @UpperTheory.Reformulated.B.Qk16.aux5 n ε : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ }

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk16.toM :
    {n : ℕ} → {ε : Fin n → Bool} → ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} {ε : Fin n → Bool} (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦
      (↑(↑g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

private theorem UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * UpperTheory.Reformulated.B.Qk16.Jm ε = 1 := by
  unfold UpperTheory.Reformulated.B.Qk16.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

private theorem UpperTheory.Reformulated.B.Qk16.left_inv {n : ℕ} (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : UpperTheory.Reformulated.B.Qk16.inUJ ε A) :
    UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = 1 := by
  have h : A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε := hA
  calc UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A
      = UpperTheory.Reformulated.B.Qk16.Jm ε * (A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, UpperTheory.Reformulated.B.Qk16.Jm_mul_Jm]

theorem UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsClosedEmbedding fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g := by
  intro n ε
  have hc : Continuous fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g :=
    Units.continuous_val.comp continuous_subtype_val
  refine ⟨?_, ?_⟩
  · let F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
      fun A ↦ (A, MulOpposite.op (UpperTheory.Reformulated.B.Qk16.Jm ε * A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε))
    have hF : Continuous F :=
      continuous_id.prodMk (MulOpposite.continuous_op.comp
        ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
    refine Topology.IsEmbedding.of_comp hc hF ?_
    have he : Topology.IsEmbedding
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) :=
      Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
    have heq : (F ∘ fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        ((Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘
          (Subtype.val : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε) → (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      funext g
      have hg : UpperTheory.Reformulated.B.Qk16.inUJ ε (g.1 : Matrix (Fin n) (Fin n) ℂ) := g.2
      have h := Units.inv_eq_of_mul_eq_one_left (UpperTheory.Reformulated.B.Qk16.left_inv ε hg)
      rw [Function.comp_apply, Function.comp_apply, Units.embedProduct_apply, h]
    rw [heq]
    exact he
  · have hr : Set.range (fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g) =
        {A | A.conjTranspose * UpperTheory.Reformulated.B.Qk16.Jm ε * A = UpperTheory.Reformulated.B.Qk16.Jm ε} := by
      ext A
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hA
        have h := UpperTheory.Reformulated.B.Qk16.left_inv ε (A := A) hA
        exact ⟨⟨⟨A, _, mul_eq_one_comm.mp h, h⟩, hA⟩, rfl⟩
    rw [hr]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
