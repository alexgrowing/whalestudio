import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeDistributionContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianLatticeThetaIntegralFormula

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrAvgAdm

theorem avg_exists_clm : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (Λ : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F Λ = Fintype.card κ → ∀ (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), (∀ j, u j ∈ Λ) →
    LinearIndependent F (fun j => (u j).1) → (∀ v ∈ Λ, ∃ c : Fin r → F, v.1 = ∑ j, c j • (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ (ι : Type) [Fintype ι] (w : ι → (κ → F) × (κ → F)), (∀ i j, (w i).1 ⬝ᵥ (w j).2 = (w j).1 ⬝ᵥ (w i).2) →
    (∀ c : ι → F, (∀ v ∈ Λ, (∑ i, c i • w i).1 ⬝ᵥ v.2 = v.1 ⬝ᵥ (∑ i, c i • w i).2) → c = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫ t, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) (pureA F (⇑f) g)) 0 ∂μ ∂ν = T f := by
  intro F _ _ ψ hψ κ _ Λ hΛ hdim r u hu hli hspan μ hμ ι _ w hw htriv ν hν g hg
  haveI := GlobalTheory.schwartzMap_barrelledSpace (κ → mixedEmbedding.mixedSpace F)
  have key : ∀ t : ι → AF F, ∃ S : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k))))
        (schr ψ (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k))))
          (pureA F (⇑f) g)) 0 ∂μ = S f := by
    intro t
    obtain ⟨A, g', hg', hA⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ
      (∑ i, t i • ((fun k => algebraMap F (AF F) ((w i).1 k)), (fun k => algebraMap F (AF F) ((w i).2 k)))) hg
    obtain ⟨T, hT⟩ := GlobalTheory.T.schrodinger_lattice_distribution_continuous F ψ hψ κ r u hli μ hμ g' hg'
    exact ⟨T.comp A, fun f => by rw [hA f, hT (A f), ContinuousLinearMap.comp_apply]⟩
  choose S hS using key
  have hint : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Integrable (fun t => S t f) ν := by
    intro f
    have hmem : pureA F (⇑f) g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
    have h := GlobalTheory.T.lagrangian_lattice_theta_integral_formula F ψ hψ κ Λ hΛ hdim r u hu hli hspan μ hμ ι w hw htriv ν hν _ hmem
    simpa only [hS] using h
  obtain ⟨L, hL⟩ := @GlobalTheory.ThetaIntAdm.exists_clm_integral _ _ _ _ _ _ _ _ (borel _) ν S hint
  exact ⟨L, fun f => by rw [hL]; simp only [hS]⟩

end GlobalTheory.LagrAvgAdm
