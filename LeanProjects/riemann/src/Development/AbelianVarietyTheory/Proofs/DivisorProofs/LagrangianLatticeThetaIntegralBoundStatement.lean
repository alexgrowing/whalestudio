import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianLatticeThetaIntegralBound
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
theorem _root_.GlobalTheory.T.lagrangian_lattice_theta_integral_bound : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (Λ : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F Λ = Fintype.card κ → ∀ (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), (∀ j, u j ∈ Λ) →
    LinearIndependent F (fun j => (u j).1) → (∀ v ∈ Λ, ∃ c : Fin r → F, v.1 = ∑ j, c j • (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ (ι : Type) [Fintype ι] (w : ι → (κ → F) × (κ → F)), (∀ i j, (w i).1 ⬝ᵥ (w j).2 = (w j).1 ⬝ᵥ (w i).2) →
    (∀ c : ι → F, (∀ v ∈ Λ, (∑ i, c i • w i).1 ⬝ᵥ v.2 = v.1 ⬝ᵥ (∑ i, c i • w i).2) → c = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫ t, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) (pureA F (⇑f) g)) 0 ∂μ ∂ν = T f := by
  first | exact @GlobalTheory.LagrAvgAdm.avg_exists_clm | exact GlobalTheory.LagrAvgAdm.avg_exists_clm | (intros; apply GlobalTheory.LagrAvgAdm.avg_exists_clm <;> assumption)
