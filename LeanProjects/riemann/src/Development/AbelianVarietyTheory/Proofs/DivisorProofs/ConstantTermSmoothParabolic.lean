import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivRealOneParamProductLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFamiStatement

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.ConstTermSmooth

theorem isSm_of_isConstTermOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ),
    ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsSm σ J c := by
  intro F E _ _ _ _ _ σ h n J hJ r C d hC H K φ c hH hφ hc
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hH hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hl
  obtain ⟨dd, δ, hδ, hW⟩ := GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary F E σ h n J hJ
  intro k γ hγ g
  have := GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily hco (fun x t => φ (x * (List.ofFn fun i => γ i (t i)).prod))
    (fun γ' hγ' x t => by simp only [mul_assoc]; exact hl γ' hγ' _) (fun x => hφ.smooth k γ hγ x)
    (GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction F E σ h n J hJ dd δ hδ hW φ hφ.level hφ.smooth k γ hγ) g
  simpa [e, GlobalTheory.Cusp.constTermOn_mul_right] using this

end GlobalTheory.ConstTermSmooth

end
