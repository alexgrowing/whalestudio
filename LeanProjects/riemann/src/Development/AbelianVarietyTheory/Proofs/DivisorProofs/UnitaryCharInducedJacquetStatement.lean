import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharInducedJacquet
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_char_induced_jacquet : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ), m + 2 = a + a' → a' < a → ∀ (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) → (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) →
    ∀ (P P₁ : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
      (π : Representation ℂ (GL (Fin (a + a')) k) P) (σ₁ : Representation ℂ (GL (Fin m) k) P₁),
      IsSmooth π → Nonempty (π.Equiv (prod₂ (detRep (Fin a) α₀) (detRep (Fin a') β₀))) → σ₁.IsIrreducible →
      ∀ (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin (a + a')) (ξ₁ ξ₂ : kˣ →* ℂˣ)
        (A A' : P →ₗ[ℂ] (GL (Fin (a + a')) k → P₁)),
        IsGLIndMap e π σ₁ ξ₁ ξ₂ A → IsGLIndMap e π σ₁ ξ₁ ξ₂ A' → A = 0 ∨ ∃ c : ℂ, A' = c • A := by
  first | exact @GlobalTheory.IndLineGL.proportional_of_glInd | exact GlobalTheory.IndLineGL.proportional_of_glInd | (intros; apply GlobalTheory.IndLineGL.proportional_of_glInd <;> assumption)
