import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementSecond
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_complement_second : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      (∃ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ ∧ μ 𝓕 = 1) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ (f fa : UA σ W.J → ℂ), Continuous f → (∀ γ ∈ ratU σ W.J, ∀ x, f (γ * x) = f x) → IsCT H f fa →
      ∀ c'' : GAd σ (c₀ • W.J.map σ) → ℂ,
      GlobalTheory.StdPar.IsConstAlong σ (c₀ • W.J.map σ) X' (insert 0 (S'.map (Fin.succEmb r))) (fun x => f ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm x)) c'' →
      ∀ (μ₁ : Measure (GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S')) (𝓕₁ : Set (GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S')),
        μ₁.IsHaarMeasure → IsFundamentalDomain ((ratPts σ (c₀ • W₁.J.map σ)).subgroupOf (GlobalTheory.StdPar.unip σ (c₀ • W₁.J.map σ) Xf S')) 𝓕₁ μ₁ →
        μ₁ 𝓕₁ = 1 → ∀ G : UA σ W.J,
        c'' (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ G) = ∫ u in 𝓕₁, fa (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm (u : GAd σ (c₀ • W₁.J.map σ))) * G) ∂μ₁ := by
  first | exact @GlobalTheory.ConstStageFlag.constTerm_stage | exact GlobalTheory.ConstStageFlag.constTerm_stage | (intros; apply GlobalTheory.ConstStageFlag.constTerm_stage <;> assumption)
