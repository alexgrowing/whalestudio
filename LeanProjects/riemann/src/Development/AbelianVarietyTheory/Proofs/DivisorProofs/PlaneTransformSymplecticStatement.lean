import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformSymplectic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_transform_symplectic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w w' : Matrix (Fin n) (Fin d) (AE F E),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
      (planeT σ X W H H' w).1.1 ⬝ᵥ (planeT σ X W H H' w').1.2 - (planeT σ X W H H' w').1.1 ⬝ᵥ (planeT σ X W H H' w).1.2 +
        symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (planeT σ X W H H' w).2 (planeT σ X W H H' w').2 := by
  first | exact @GlobalTheory.ThK.PlaneForm.form_eq | exact GlobalTheory.ThK.PlaneForm.form_eq | (intros; apply GlobalTheory.ThK.PlaneForm.form_eq <;> assumption)
