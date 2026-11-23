import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFiniteLocalApproxTheta
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_finite_local_approx_theta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ hf ∈ UAt σ W (fun u : AF F => u.2), ∀ h : Pl F → UA σ W.J,
      (∀ v, h v ∈ UAt σ W (evFin F v) ∧ ∀ u : AF F, At (evFin F v) u → u • mat (h v) = u • mat hf) →
      ∃ S : Finset (Pl F), ∀ T : Finset (Pl F), S ⊆ T → ∀ (f : SInf F (Fin n × Fin d))
        (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) →
        ∃ φ₁ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ,
          (∀ v, φ₁ v ∈ SB _ ∧ Acts (evFin F v) (om (1, h v)) (φ v) (φ₁ v)) ∧ (∀ v ∉ T, φ₁ v = M.vac v) ∧
          om (1, hf) (pure f φ) = pure f φ₁ := by
  first | exact @GlobalTheory.FinFactor.om_pure_factor | exact GlobalTheory.FinFactor.om_pure_factor | (intros; apply GlobalTheory.FinFactor.om_pure_factor <;> assumption)
