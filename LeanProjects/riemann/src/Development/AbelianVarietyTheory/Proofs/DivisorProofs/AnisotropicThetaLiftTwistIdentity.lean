import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairAnisotropicThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairAnisotropicThetaRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairAnisotropicThetaFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairAnisotropicThetaGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairAnisotropicThetaUnfoldStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.SmoothDiff

theorem isSmoothModerate_diff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ c : ℂ, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
    ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
      (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
      GlobalTheory.SiegelSet.IsSmoothModerate σ (c₀ • G.W.J.map σ) φ' := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ'
  exact ⟨GlobalTheory.T.matched_pair_anisotropic_theta hK F E σ B a a' G X om om' R Rf hM hq hp c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ',
    GlobalTheory.T.matched_pair_anisotropic_theta_real hK F E σ B a a' G X om om' R Rf hM hq hp c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ',
    GlobalTheory.T.matched_pair_anisotropic_theta_finite hK F E σ B a a' G X om om' R Rf hM hq hp c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ',
    GlobalTheory.T.matched_pair_anisotropic_theta_global hK F E σ B a a' G X om om' R Rf hM hq hp c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ',
    GlobalTheory.T.matched_pair_anisotropic_theta_unfold hK F E σ B a a' G X om om' R Rf hM hq hp c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ'⟩

end GlobalTheory.ThK.SmoothDiff
