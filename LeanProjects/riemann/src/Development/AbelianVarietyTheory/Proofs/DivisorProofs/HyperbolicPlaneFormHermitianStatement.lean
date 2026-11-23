import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormHermitian
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_form_hermitian : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (χa χb : Chr F E) (za zb : ℝ) (Kh : Set (UA σ W.J)) (S : Submodule ℂ (UA σ W.J → ℂ)),
      BetaZero W₁ H χa χb za zb S → (∀ f ∈ S, Continuous f ∧ ∀ γ ∈ ratU σ W.J, ∀ x, f (γ * x) = f x) →
      (∀ f ∈ S, ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • W.J.map σ) → ∀ φ' : GAd σ (c₀ • W.J.map σ) → ℂ,
        (∀ (g : UA σ W.J) (g' : GAd σ (c₀ • W.J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) Xf Yf →
          ∀ S' : Finset (Fin r), ¬ (∀ k ∈ S', ∀ l ≤ k, l ∈ S') → GlobalTheory.StdPar.IsCuspComp σ (c₀ • W.J.map σ) Xf Yf S' K φ' 0) →
      ∀ f ∈ alphaSpan W₁ H χa χb za zb Kh S, ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • W₁.J.map σ) →
        ∀ φ' : GAd σ (c₀ • W₁.J.map σ) → ℂ, (∀ (g : UA σ W₁.J) (g' : GAd σ (c₀ • W₁.J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
          ∀ S' : Finset (Fin r), ¬ (∀ k ∈ S', ∀ l ≤ k, l ∈ S') → GlobalTheory.StdPar.IsCuspComp σ (c₀ • W₁.J.map σ) Xf Yf S' K φ' 0 := by
  first | exact @GlobalTheory.ThK.DescStepCusp.cuspComp_alphaSpan_eq_zero | exact GlobalTheory.ThK.DescStepCusp.cuspComp_alphaSpan_eq_zero | (intros; apply GlobalTheory.ThK.DescStepCusp.cuspComp_alphaSpan_eq_zero <;> assumption)
