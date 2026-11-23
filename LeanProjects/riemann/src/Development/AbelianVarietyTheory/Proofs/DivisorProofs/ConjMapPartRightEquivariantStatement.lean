import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_map_part_right_equivariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (∀ x, ‖ψ x‖ = 1) →
    ∀ (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
      (A₁ B₁ A₂ B₂ : κ → AF F) (a b : κ₁ → AF F),
      (∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) →
      ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
        schr ψ (Sum.elim a a, Sum.elim b (-b)) (evDbl T φ) := by
  first | exact @GlobalTheory.DoublingEvLaw.main | exact GlobalTheory.DoublingEvLaw.main | (intros; apply GlobalTheory.DoublingEvLaw.main <;> assumption)
