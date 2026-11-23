import Mathlib

noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.cT :
    {A : Type} → [inst : CommRing A] → (A →+* A) → {m p : Type} → Matrix m p A → Matrix p m A :=
    fun {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) ↦ (M.map (⇑σ : A → A)).transpose

private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    (P Q : Matrix n n A) :
    UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (P * Q) = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ Q * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ P := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (1 : Matrix n n A) = 1 := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {a b : GL n A},
      a ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
          a * b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J a b ha hb
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  rw [Units.val_mul, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑b : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑a : Matrix n n A) * J * (↑a : Matrix n n A)) * (↑b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A), UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(1 : GL n A) : Matrix n n A) * J * (↑(1 : GL n A) : Matrix n n A) = J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {g : GL n A},
      g ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        g⁻¹ ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  have h1 : (↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) = 1 := by
    rw [← UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul, h1, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A)) * (↑(g⁻¹) : Matrix n n A) := by
        rw [hg]
    _ = (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A)) * J *
        ((↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UJ :
    {A : Type} →
      [inst : CommRing A] →
        {n : Type} → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → (A →+* A) → Matrix n n A → Subgroup (GL n A) :=
    fun {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
        (J : Matrix n n A) ↦
      { carrier := {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J},
        mul_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 A inst n inst_1 inst_2 σ J, one_mem' := UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 σ J,
        inv_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 A inst n inst_1 inst_2 σ J : Subgroup (GL n A) }

noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → (n : ℕ) → Subgroup (GL (Fin n) E) :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (n : ℕ) ↦
      UpperTheory.Reformulated.B.CocycleMultiplicative.UJ (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom (1 : Matrix (Fin n) (Fin n) E)

open scoped Matrix.Norms.L2Operator in
private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : star A * A = 1) {z : ℂ} (hz : z ∈ spectrum ℂ A) : ‖z‖ = (1 : ℝ) := by
  have hu : A ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨h, mul_eq_one_comm.mp h⟩
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with hs | hn
  · exact absurd hz (by simp [spectrum.of_subsingleton])
  · simpa using spectrum.subset_circle_of_unitary hu hz

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.norm_eq_one_of_root :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {n : ℕ}
      (γ : ↥(UpperTheory.Reformulated.B.CocycleMultiplicative.UE E n)) (τ : E →+* ℂ),
      ∀ z ∈ (Polynomial.map τ (↑(↑γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly).roots, ‖z‖ = (1 : ℝ) := by
  intro E _ _ _ n γ τ z hz
  have hγ := γ.2
  obtain ⟨g, hg⟩ := γ
  simp only at hz
  have hg' : UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
      (↑g : Matrix (Fin n) (Fin n) E) * 1 * (↑g : Matrix (Fin n) (Fin n) E) = 1 := hg
  rw [Matrix.mul_one] at hg'
  have hroot : ((↑g : Matrix (Fin n) (Fin n) E).map τ).charpoly.IsRoot z := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.mem_roots'.mp hz).2
  have hstar : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) =
      (UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
        (↑g : Matrix (Fin n) (Fin n) E)).map τ := by
    ext i j
    simp [UpperTheory.Reformulated.B.CocycleMultiplicative.cT, Matrix.star_apply]
  have hU : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) * (↑g : Matrix (Fin n) (Fin n) E).map τ = 1 := by
    rw [hstar, ← Matrix.map_mul, hg', Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum _ hU (Matrix.mem_spectrum_of_isRoot_charpoly hroot)
