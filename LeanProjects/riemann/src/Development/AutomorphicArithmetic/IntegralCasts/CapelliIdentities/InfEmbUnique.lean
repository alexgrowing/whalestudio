import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf27.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

theorem UpperTheory.Reformulated.B.Qf27.aux2 :
    ∀ {F : Type} [inst : Field F], SMulCommClass F (UpperTheory.Reformulated.B.Qf27.Ainf F) (UpperTheory.Reformulated.B.Qf27.Ainf F) := by
  intro F _
  infer_instance

theorem UpperTheory.Reformulated.B.Qf27.aux3 :
    ∀ {F : Type} [inst : Field F], IsScalarTower F (UpperTheory.Reformulated.B.Qf27.Ainf F) (UpperTheory.Reformulated.B.Qf27.Ainf F) := by
  intro F _
  infer_instance

theorem UpperTheory.Reformulated.B.Qf27.aux4 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E], SMulCommClass F E E := by
  intro F E _ _ _
  infer_instance

theorem UpperTheory.Reformulated.B.Qf27.aux5 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E], IsScalarTower F E E := by
  intro F E _ _ _
  infer_instance

noncomputable def UpperTheory.Reformulated.B.Qf27.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qf27.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qf27.infEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {τ : E →+* ℂ}
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ τ θ θ' h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ c : F, (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F) c) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] (algebraMap F E c) := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hA : (fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h2 h2' ?_
    funext c
    simp only [Function.comp_apply]
    rw [key, h1, h1']
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
    have e : a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h1, h1', congrFun hA a]
