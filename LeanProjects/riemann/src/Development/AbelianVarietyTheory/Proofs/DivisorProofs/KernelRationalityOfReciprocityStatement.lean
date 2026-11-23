import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityOfReciprocity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_evaluation_block_transform : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ : ℕ} {κ' : Type} [Fintype κ'] (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (M₁ : Model σ X₁ W₁) (eq : Fin n × Fin d ≃ κ' ⊕ Fin n₁ × Fin d₁)
    (T : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] ((κ' → AF F) × (κ' → AF F)) × Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hf : ∀ w w', symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
        (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (T w).2 (T w').2)
    (l : ∀ v : Pl F, (κ' → Fv F v) → ℂ) (μ : Measure (UA σ X.J)) (D : Set (UA σ X.J)),
    (∀ z, T (incM F ι * z * (incM F ι')ᵀ) = ((0, 0), z)) → (∀ u ∈ I, (T u).1.1 = 0 ∧ (T u).2 = 0) →
    (∀ v, l v ∈ SB _ ∧ l v 0 = 1) → (∀ v, M₁.vac v ∈ SB _) →
    IsEv B (Model.mk (glueDarboux M₁.co eq T hf) (fun v => vacGlue eq (l v) (M₁.vac v)) μ D) M₁ ι ι' I (restr eq) := by
  first | exact @GlobalTheory.ThK.PlaneCo.GlueEv.restr_isEv | exact GlobalTheory.ThK.PlaneCo.GlueEv.restr_isEv | (intros; apply GlobalTheory.ThK.PlaneCo.GlueEv.restr_isEv <;> assumption)
