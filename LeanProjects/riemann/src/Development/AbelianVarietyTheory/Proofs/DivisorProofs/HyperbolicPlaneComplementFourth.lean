import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularQuotientIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneModularCharacterStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.ThK.DescGenCusp

theorem integral_leviOne_eq_zero_of_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ (A : GAd σ (c₀ • W.J.map σ) → ℂ) (a : GAd σ (c₀ • W₁.J.map σ) → ℂ),
      (∀ (t : (AE F E)ˣ) (m : UA σ W.J) (y : GAd σ (c₀ • W₁.J.map σ)), IsLevi (W₁ := W₁) H t 1 m → GlobalTheory.Doubling.absE F E t = 1 →
        A (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (m * M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm y))) = a y) →
      (∀ (μ : Measure (GlobalTheory.StdPar.leviOne σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))))) (𝓕 : Set (GlobalTheory.StdPar.leviOne σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))))),
        μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ (c₀ • W.J.map σ)).subgroupOf (GlobalTheory.StdPar.leviOne σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))))) 𝓕 μ →
        IntegrableOn (fun m : GlobalTheory.StdPar.leviOne σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r))) => A m) 𝓕 μ ∧
        ∫ m in 𝓕, A m ∂μ = 0) →
      ∀ (μ₁ : Measure (GlobalTheory.StdPar.leviOne σ (c₀ • W₁.J.map σ) Xf Yf S')) (𝓕₁ : Set (GlobalTheory.StdPar.leviOne σ (c₀ • W₁.J.map σ) Xf Yf S')),
        μ₁.IsHaarMeasure → IsFundamentalDomain ((ratPts σ (c₀ • W₁.J.map σ)).subgroupOf (GlobalTheory.StdPar.leviOne σ (c₀ • W₁.J.map σ) Xf Yf S')) 𝓕₁ μ₁ →
        IntegrableOn (fun m : GlobalTheory.StdPar.leviOne σ (c₀ • W₁.J.map σ) Xf Yf S' => a m) 𝓕₁ μ₁ ∧
        ∫ m in 𝓕₁, a m ∂μ₁ = 0 := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH M hMc hML hMr r Xf Yf hW₁ X' Y' hW'
    hx0 hy0 hsucc S' A a hAa hA μ₁ 𝓕₁ hμ₁ h𝓕₁
  obtain ⟨T, φ, hTc, hTl, hφ, hrat⟩ := GlobalTheory.T.skew_plane_modular_character F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hH₁ hH M hMc hML hMr
    r Xf Yf hW₁ X' Y' hW' hx0 hy0 hsucc S'
  haveI : LocallyCompactSpace T := hTc.locallyCompactSpace
  haveI : LocallyCompactSpace (GlobalTheory.StdPar.leviOne σ (c₀ • W₁.J.map σ) Xf Yf S') :=
    (GlobalTheory.StdPar.isClosed_levi (S := S') (h := hCM) (hJ := hH₁) (hW := hW₁)).2.locallyCompactSpace
  refine GlobalTheory.T.unimodular_quotient_integral_formula _ T _ φ ((ratPts σ (c₀ • W.J.map σ)).subgroupOf _) ((ratPts σ (c₀ • W.J.map σ)).subgroupOf T)
    ((ratPts σ (c₀ • W₁.J.map σ)).subgroupOf _) (fun p => by simp only [Subgroup.mem_subgroupOf]; exact hrat p)
    (fun m => A m) (fun m => a m) (fun p => ?_) hA μ₁ 𝓕₁ hμ₁ h𝓕₁
  obtain ⟨t, ht, hl⟩ := hTl p.1
  show A (φ p : GAd σ (c₀ • W.J.map σ)) = a p.2
  rw [hφ p, ← (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).apply_symm_apply (p.1 : GAd σ (c₀ • W.J.map σ)), ← map_mul]
  exact hAa t _ _ hl ht

end GlobalTheory.ThK.DescGenCusp
