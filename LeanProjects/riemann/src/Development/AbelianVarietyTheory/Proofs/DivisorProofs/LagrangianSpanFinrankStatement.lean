import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSpanFinrank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_span_finrank : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (Λ : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F Λ = Fintype.card κ →
    ∀ (ι : Type) [Fintype ι] (w : ι → (κ → F) × (κ → F)), (∀ i j, (w i).1 ⬝ᵥ (w j).2 = (w j).1 ⬝ᵥ (w i).2) →
    (∀ c : ι → F, (∀ v ∈ Λ, (∑ i, c i • w i).1 ⬝ᵥ v.2 = v.1 ⬝ᵥ (∑ i, c i • w i).2) → c = 0) →
    ∀ l ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ v ∈ Λ, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))) φ) = l φ) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      (∀ φ ∈ schA F κ, Integrable (fun t : ι → AF F =>
          l (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ)) ν) ∧
      ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = ∫ t, l (schr ψ (∑ i, t i •
          ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) φ) ∂ν := by
  first | exact @GlobalTheory.LagrangianAverage.main | exact GlobalTheory.LagrangianAverage.main | (intros; apply GlobalTheory.LagrangianAverage.main <;> assumption)
