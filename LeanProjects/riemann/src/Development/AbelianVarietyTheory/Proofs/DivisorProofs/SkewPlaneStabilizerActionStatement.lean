import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneStabilizerAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_plane_stabilizer_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (X' Y' : Matrix (Fin n) (Fin (r + 1)) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) →
      ∃ (P : Subgroup (GAd σ (c₀ • W.J.map σ))) (π : P →* GAd σ (c₀ • W₁.J.map σ)) (T : P →* (AE F E)ˣ),
        (∀ p, p ∈ P ↔ ∃ t : AF F ⊗[F] E, (matHom _ σ _ p).1 *ᵥ (fun i => inclR (F := F) (AF F) (H.x i)) = t • fun i => inclR (F := F) (AF F) (H.x i)) ∧
        (∀ p : P, ∃ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∃ m, IsLevi (W₁ := W₁) H (T p) 1 m ∧
          (p : GAd σ (c₀ • W.J.map σ)) = u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M (π p)) ∧
        (∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∀ t m y, IsLevi (W₁ := W₁) H t 1 m →
          u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ P) ∧
        Continuous π ∧ Continuous T ∧
        ∃ A : Matrix (Fin n₁) (Fin n) E, A * H.ι = 1 ∧ ∀ p : P, (matHom _ σ _ (π p)).1 =
          GlobalTheory.SiegelSet.adMat F A * (matHom _ σ _ (p : GAd σ (c₀ • W.J.map σ))).1 * GlobalTheory.SiegelSet.adMat F H.ι := by
  first | exact @GlobalTheory.StabLine.exists_stab_decomp | exact GlobalTheory.StabLine.exists_stab_decomp | (intros; apply GlobalTheory.StabLine.exists_stab_decomp <;> assumption)
