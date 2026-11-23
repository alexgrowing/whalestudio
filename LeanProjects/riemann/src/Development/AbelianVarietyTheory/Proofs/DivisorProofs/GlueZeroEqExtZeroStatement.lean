import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueZeroEqExtZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_adapted_good_model : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ (eq : Fin n × Fin d ≃ Kc F E d₁ n₁ ⊕ Fin n₁ × Fin d₁)
      (T : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] ((Kc F E d₁ n₁ → AF F) × (Kc F E d₁ n₁ → AF F)) × Matrix (Fin n₁) (Fin d₁) (AE F E))
      (hT : ∀ u, T u = planeT σ X W H H' u)
      (hf : ∀ w w', symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
        (T w).1.1 ⬝ᵥ (T w').1.2 - (T w').1.1 ⬝ᵥ (T w).1.2 + symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (T w).2 (T w').2)
      (μ : Measure (UA σ X.J)) (D : Set (UA σ X.J)) (v : Pl F),
      Model.IsVac (Model.mk (glueDarboux M₁.co eq T hf) (fun v => vacGlue eq (vacS σ X W H H' v) (M₁.vac v)) μ D) B.ψ v
        (vacGlue eq (vacS σ X W H H' v) (M₁.vac v)) := by
  first | exact @GlobalTheory.ThK.PlaneCo.isVac_vacGlue | exact GlobalTheory.ThK.PlaneCo.isVac_vacGlue | (intros; apply GlobalTheory.ThK.PlaneCo.isVac_vacGlue <;> assumption)
