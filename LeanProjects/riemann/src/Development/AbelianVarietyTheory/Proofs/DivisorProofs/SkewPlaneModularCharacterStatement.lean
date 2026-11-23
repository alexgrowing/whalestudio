import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneModularCharacter
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
theorem _root_.GlobalTheory.T.skew_plane_modular_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
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
      ∃ (T : Subgroup (GAd σ (c₀ • W.J.map σ)))
        (φ : T × GlobalTheory.StdPar.leviOne σ (c₀ • W₁.J.map σ) Xf Yf S' ≃ₜ*
          GlobalTheory.StdPar.leviOne σ (c₀ • W.J.map σ) X' Y' (insert 0 (S'.map (Fin.succEmb r)))),
        IsClosed (T : Set (GAd σ (c₀ • W.J.map σ))) ∧
        (∀ τ : T, ∃ t : (AE F E)ˣ, GlobalTheory.Doubling.absE F E t = 1 ∧
          IsLevi (W₁ := W₁) H t 1 ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm τ)) ∧
        (∀ p, ((φ p : GAd σ (c₀ • W.J.map σ))) = (p.1 : GAd σ (c₀ • W.J.map σ)) *
          GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm p.2))) ∧
        (∀ p, (φ p : GAd σ (c₀ • W.J.map σ)) ∈ ratPts σ (c₀ • W.J.map σ) ↔
          (p.1 : GAd σ (c₀ • W.J.map σ)) ∈ ratPts σ (c₀ • W.J.map σ) ∧
          (p.2 : GAd σ (c₀ • W₁.J.map σ)) ∈ ratPts σ (c₀ • W₁.J.map σ)) := by
  first | exact @GlobalTheory.LeviSplit.leviOne_prod | exact GlobalTheory.LeviSplit.leviOne_prod | (intros; apply GlobalTheory.LeviSplit.leviOne_prod <;> assumption)
