import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetSmoothModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicThetaLiftTwistIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicThetaLiftNonvanishingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKOrthDecay

theorem decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → fa = c • fa' ∧ fb = c • fb') →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hprop Φ Φ' hΦ' hPM hCT N
  have hcm : IsCMExt F E σ := hM.triple.base.cm
  obtain ⟨c₀, hc₀, hJ⟩ := GlobalTheory.T.skew_hermitian_twist_to_hermitian F E σ hcm B (a + a') G.W _ _ hM.triple.geo.hW
  have heq := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := G.W.J) (GlobalTheory.SiegelSet.sigma_sigma hcm) hc₀
  let f : UA σ G.W.J → ℂ := fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h
  let φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ := fun g' => f ⟨g'.1, (SetLike.ext_iff.1 heq g'.1).2 g'.2⟩
  have hφ' : ∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 →
      φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g := by
    intro g g' e
    show f _ = f g
    congr 1
    exact Subtype.ext e.symm
  exact GlobalTheory.T.siegel_set_smooth_moderate_growth hKP.siegelSetUnitary F E σ hcm _ G.W.J c₀ hc₀ hJ f φ' hφ'
    (GlobalTheory.T.anisotropic_theta_lift_twist_identity hKP F E σ B a a' G X om om' R Rf hM hq hp c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ')
    (GlobalTheory.T.anisotropic_theta_lift_nonvanishing hKP F E σ B a a' G X om om' R Rf hM hq hp d₁ W₁ H' i₀ i₁ hH' c hprop Φ Φ' hΦ' hPM hCT c₀ hc₀ φ' hφ') N

end GlobalTheory.ThKOrthDecay
