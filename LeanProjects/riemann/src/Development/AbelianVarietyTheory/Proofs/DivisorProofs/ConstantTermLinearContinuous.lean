import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.CuspCompZeroLin

theorem isCuspComp_sub_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (S : Finset (Fin r)) (φ₁ φ₂ : GAd σ J → ℂ) (z : ℂ),
        Continuous φ₁ → Continuous φ₂ → (∀ γ ∈ GlobalTheory.AdelicU.ratPts σ J, ∀ g, φ₁ (γ * g) = φ₁ g) →
        (∀ γ ∈ GlobalTheory.AdelicU.ratPts σ J, ∀ g, φ₂ (γ * g) = φ₂ g) →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₁ 0 → GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ₂ 0 →
        GlobalTheory.StdPar.IsCuspComp σ J X Y S K (fun g => φ₁ g - z * φ₂ g) 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW K S φ₁ φ₂ z hc1 hc2 hr1 hr2 H1 H2
  obtain ⟨-, c₁, hC1, hs1⟩ := H1
  obtain ⟨-, c₂, hC2, hs2⟩ := H2
  have hint : ∀ (f : GAd σ J → ℂ), Continuous f → (∀ γ ∈ ratPts σ J, ∀ g, f (γ * g) = f g) →
      ∀ (μ : Measure (GlobalTheory.StdPar.unip σ J X S)) (𝓕 : Set (GlobalTheory.StdPar.unip σ J X S)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.unip σ J X S)) 𝓕 μ → ∀ g,
      IntegrableOn (fun u : GlobalTheory.StdPar.unip σ J X S => f ((u : GAd σ J) * g)) 𝓕 μ := by
    intro f hf hfi μ 𝓕 hμ h𝓕 g
    obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hcm n J hJ r X Y hW S
    exact GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ _ C hC hcov μ hμ 𝓕 h𝓕 _ (by fun_prop) fun γ hγ u => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hfi _ (Subgroup.mem_subgroupOf.1 hγ) _
  refine ⟨⟨GlobalTheory.StdPar.isAutOn_const σ J X Y S K 0, fun S' _ => GlobalTheory.StdPar.isConstAlong_const σ J X S' 0⟩,
    fun g => c₁ g - z * c₂ g, fun μ 𝓕 hμ h𝓕 hone g => ?_, fun ψ hψ μ 𝓕 hμ h𝓕 g g' => ?_⟩
  · have e1 := hC1 μ 𝓕 hμ h𝓕 hone g
    have e2 := hC2 μ 𝓕 hμ h𝓕 hone g
    have i1 := hint φ₁ hc1 hr1 μ 𝓕 hμ h𝓕 g
    have i2 := hint φ₂ hc2 hr2 μ 𝓕 hμ h𝓕 g
    rw [integral_sub i1 (i2.const_mul z), integral_const_mul, ← e1, ← e2]
  · obtain ⟨i1, -, e1⟩ := hs1 ψ hψ μ 𝓕 hμ h𝓕 g g'
    obtain ⟨i2, -, e2⟩ := hs2 ψ hψ μ 𝓕 hμ h𝓕 g g'
    simp only [Pi.zero_apply, zero_mul, integral_zero] at e1 e2
    refine ⟨?_, by simp, ?_⟩
    · exact (i1.sub (i2.const_mul z)).congr (Filter.Eventually.of_forall fun m => by simp only [Pi.sub_apply]; ring)
    · have l : ∫ m in 𝓕, (c₁ ((m : GAd σ J) * g) - z * c₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ =
          (∫ m in 𝓕, c₁ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ) -
            z * ∫ m in 𝓕, c₂ ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ := by
        rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul z)]
        congr 1
        funext m
        ring
      show ∫ m in 𝓕, (c₁ ((m : GAd σ J) * g) - z * c₂ ((m : GAd σ J) * g)) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ =
        ∫ m in 𝓕, (0 : GAd σ J → ℂ) ((m : GAd σ J) * g) * (starRingEnd ℂ) (ψ ((m : GAd σ J) * g')) ∂μ
      simp only [Pi.zero_apply, zero_mul, integral_zero]
      rw [l, e1, e2, mul_zero, sub_zero]

end GlobalTheory.CuspCompZeroLin
