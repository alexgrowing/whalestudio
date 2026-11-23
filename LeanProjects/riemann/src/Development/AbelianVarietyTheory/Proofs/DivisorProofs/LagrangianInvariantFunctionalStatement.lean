import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFunctional
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_invariant_functional : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L = Fintype.card κ →
    ∀ l ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ, l (schr ψ (t • GlobalTheory.SiegelConv.ratP w) φ) = l φ) →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (A : (m → F) →ₗ[F] (κ → F) × (κ → F)), (∀ s, A s ∈ L → s = 0) →
    ∀ μ : @Measure (m → AF F) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ φ ∈ schA F κ, (letI : MeasurableSpace (m → AF F) := borel _; Integrable (fun t => l (schr ψ (GlobalTheory.SiegelConv.extA A t) φ)) μ) := by
  first | exact @GlobalTheory.SiegelLagr.main | exact GlobalTheory.SiegelLagr.main | (intros; apply GlobalTheory.SiegelLagr.main <;> assumption)
