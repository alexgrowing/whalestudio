import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralSmoothAlongRealLinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralPolynomialGrowthStatement

noncomputable section

namespace GlobalTheory.ThKAutVGrowth

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

theorem uniformGrowth_thetaIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∃ N : ℕ, ∀ l : List (ℝ → GAd σ (c • G.W.J.map σ)), (∀ γ ∈ l, IsRealLine σ (c • G.W.J.map σ) γ) → ∃ C : ℝ, ∀ g, ‖l.foldr lineDer (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) g‖ ≤ C * (height σ (c • G.W.J.map σ) g : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ
  obtain ⟨N, hN⟩ := GlobalTheory.T.theta_integral_polynomial_growth F E σ hσ B a a' G X om om' hKP hT c hc hcs
  refine ⟨N, fun l hl => ?_⟩
  obtain ⟨Φ₁, h1, e⟩ : ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, l.foldr lineDer (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) =
      fun x => G.M.I om Φ₁ ((toGAd hσ G.W.J hc).symm x) := by
    induction l with
    | nil => exact ⟨Φ, hΦ, rfl⟩
    | cons γ l ih =>
      obtain ⟨Φ₂, h2, e2⟩ := ih (fun γ' hγ' => hl γ' (List.mem_cons_of_mem _ hγ'))
      obtain ⟨Φ₃, h3, e3⟩ := GlobalTheory.T.theta_integral_smooth_along_real_lines F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ₂ h2 γ (hl γ List.mem_cons_self)
      exact ⟨Φ₃, h3, by rw [List.foldr_cons, e2, e3]⟩
  obtain ⟨C, hC⟩ := hN Φ₁ h1
  exact ⟨C, fun g => by rw [e]; exact hC g⟩

end GlobalTheory.ThKAutVGrowth

end
