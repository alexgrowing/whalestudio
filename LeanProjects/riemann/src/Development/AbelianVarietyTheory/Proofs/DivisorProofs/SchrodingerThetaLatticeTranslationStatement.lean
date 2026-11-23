import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerThetaLatticeTranslation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_theta_lattice_translation : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] (Λ : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → ∀ (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), (∀ j, u j ∈ Λ) →
    (∀ v ∈ Λ, ∃ c : Fin r → F, v.1 = ∑ j, c j • (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (t : AF F), ∀ v ∈ Λ, ∀ φ : (κ → AF F) → ℂ,
      ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) (schr ψ (t • ((fun k => algebraMap F (AF F) (v.1 k)), (fun k => algebraMap F (AF F) (v.2 k)))) φ) 0 ∂μ = ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ := by
  first | exact @GlobalTheory.LagrInv.lagrForm_schr_invariant | exact GlobalTheory.LagrInv.lagrForm_schr_invariant | (intros; apply GlobalTheory.LagrInv.lagrForm_schr_invariant <;> assumption)
