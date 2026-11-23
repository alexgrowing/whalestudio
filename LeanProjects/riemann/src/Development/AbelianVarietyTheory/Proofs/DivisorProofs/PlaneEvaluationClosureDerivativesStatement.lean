import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneEvaluationClosureDerivatives
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_evaluation_closure_derivatives : ∀ (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2) (P₁ : Submodule ℂ (SInf F (Fin n × Fin d₁)))
    (G : Set (SInf F (Fin n × Fin d))), HasDH F (Fin n × Fin d) →
    (∀ (a b : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F), ∀ g ∈ P₁, ∀ g₁ : SInf F (Fin n × Fin d₁), ⇑g₁ = dH a b ⇑g → g₁ ∈ P₁) →
    (∀ f₀ ∈ G, ei F hd f₀ ∈ P₁ ∧ ∀ γ : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd γ →
      ∃ β : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd β ∧ ∃ c : ℂ, ∀ x, dH γ 0 ⇑f₀ x = c * dH 0 β ⇑f₀ x) →
    ∃ Q : Submodule ℂ (SInf F (Fin n × Fin d)), G ⊆ Q ∧
      (∀ (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F), ∀ f ∈ Q, ∀ f₁ : SInf F (Fin n × Fin d), ⇑f₁ = dH a b ⇑f → f₁ ∈ Q) ∧
      ∀ f ∈ Q, ei F hd f ∈ P₁ := by
  first | exact @GlobalTheory.ThK.PlaneEv.Clo.exists_dH_stable_ei_mem | exact GlobalTheory.ThK.PlaneEv.Clo.exists_dH_stable_ei_mem | (intros; apply GlobalTheory.ThK.PlaneEv.Clo.exists_dH_stable_ei_mem <;> assumption)
