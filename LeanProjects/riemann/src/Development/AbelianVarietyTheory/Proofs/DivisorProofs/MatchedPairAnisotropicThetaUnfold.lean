import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftBoundedDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRealLineDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmoothStatement

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.GrowthDiff
open GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.RealLineGrowthDerivative

theorem growth_diff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ c : ℂ, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
    ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
      (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
      ∃ N : ℕ, ∀ l : List (ℝ → GAd σ (c₀ • G.W.J.map σ)), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • G.W.J.map σ) γ) →
        ∃ C : ℝ, ∀ g, ‖l.foldr GlobalTheory.SiegelSet.lineDer φ' g‖ ≤ C * (height σ (c₀ • G.W.J.map σ) g : ℝ) ^ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM _ _ c Φ Φ' hΦ' hPM c₀ hc₀ φ' hφ'
  have hT := hM.triple
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  obtain ⟨c₁, hc₁, hc₁s⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hT.base.cm
  obtain ⟨T, -, m, m', f, φ, f', ψ, h1, h2, e1, e2, -⟩ := hPM
  have hev : ∀ {ρ : ∀ v : Pl F, Type} (φ₀ ρ₀ : ∀ v, ρ v), (∀ v ∉ T, φ₀ v = ρ₀ v) → ∀ᶠ v in cofinite, φ₀ v = ρ₀ v :=
    fun φ₀ ρ₀ h => Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => not_not.1 fun h' => hv (h v h'))
  have hP : Φ ∈ PolData B G.M := e1 ▸ Submodule.sum_mem _ fun i _ =>
    Submodule.subset_span ⟨f i, (h1 i).1, φ i, (h1 i).2.1, hev _ _ (h1 i).2.2, rfl⟩
  have hP' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := ⟨e2 ▸ Submodule.sum_mem _ fun j _ =>
    Submodule.subset_span ⟨f' j, (h2 j).1, ψ j, (h2 j).2.1, hev _ _ (h2 j).2.2, rfl⟩, hΦ'⟩
  let e : GAd σ (c₀ • G.W.J.map σ) ≃* GAd σ (c₁ • G.W.J.map σ) := (toGAd hσ G.W.J hc₀).symm.trans (toGAd hσ G.W.J hc₁)
  let fV : GAd σ (c₁ • G.W.J.map σ) → ℂ := fun x => G.M.I om Φ ((toGAd hσ G.W.J hc₁).symm x)
  let fV' : GAd σ (c₁ • G.W.J.map σ) → ℂ := fun x => G.M'.I om' Φ' ((toGAd hσ G.W.J hc₁).symm x)
  have hφe : φ' = fun x => (fun y => fV y - c * fV' y) (e x) := by
    funext x
    refine (hφ' ((toGAd hσ G.W.J hc₀).symm x) x rfl).trans ?_
    simp [fV, fV', e]
  have sV : GlobalTheory.UAut.IsSm σ (c₁ • G.W.J.map σ) fV := GlobalTheory.T.theta_lift_real_line_derivative F E σ hσ B a a' G X om om' hKP hT c₁ hc₁ hc₁s Φ hP
  have sV' : GlobalTheory.UAut.IsSm σ (c₁ • G.W.J.map σ) fV' := GlobalTheory.T.polynomial_theta_kernel_smooth F E σ hσ B a a' G X om om' hKP hT c₁ hc₁ hc₁s Φ' hP'
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.T.theta_lift_lineDer_uniform_moderate_growth F E σ hσ B a a' G X om om' hKP hT c₁ hc₁ hc₁s Φ hP
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.T.polynomial_theta_kernel_moderate_growth F E σ hσ B a a' G X om om' hKP hT c₁ hc₁ hc₁s Φ' hP'
  refine ⟨N₁ + N₂, fun l hl => ?_⟩
  have hl' : ∀ γ ∈ l.map (fun γ t => e (γ t)), IsRealLine σ (c₁ • G.W.J.map σ) γ := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hγ'
    exact isRealLine_move hσ G.W.J hc₀ hc₁ (hl γ hγ)
  obtain ⟨C₁, hC₁⟩ := hN₁ _ hl'
  obtain ⟨C₂, hC₂⟩ := hN₂ _ hl'
  refine ⟨|C₁| + ‖c‖ * |C₂|, fun g => ?_⟩
  rw [hφe, foldr_lineDer_comp e (fun y => fV y - c * fV' y), foldr_lineDer_sub sV sV' c _ hl']
  have hh : (height σ (c₁ • G.W.J.map σ) (e g) : ℝ) = height σ (c₀ • G.W.J.map σ) g := rfl
  have h1' : (1 : ℝ) ≤ height σ (c₀ • G.W.J.map σ) g := by exact_mod_cast one_le_height σ _ g
  set H := (height σ (c₀ • G.W.J.map σ) g : ℝ)
  have p1 : H ^ N₁ ≤ H ^ (N₁ + N₂) := pow_le_pow_right₀ h1' (by omega)
  have p2 : H ^ N₂ ≤ H ^ (N₁ + N₂) := pow_le_pow_right₀ h1' (by omega)
  have q1 := hC₁ (e g)
  have q2 := hC₂ (e g)
  rw [hh] at q1 q2
  have hp0 : 0 ≤ H ^ (N₁ + N₂) := by positivity
  calc ‖(l.map fun γ t => e (γ t)).foldr lineDer fV (e g) - c * (l.map fun γ t => e (γ t)).foldr lineDer fV' (e g)‖
      ≤ ‖(l.map fun γ t => e (γ t)).foldr lineDer fV (e g)‖ + ‖c‖ * ‖(l.map fun γ t => e (γ t)).foldr lineDer fV' (e g)‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
    _ ≤ |C₁| * H ^ (N₁ + N₂) + ‖c‖ * (|C₂| * H ^ (N₁ + N₂)) := by
        gcongr
        · exact q1.trans (mul_le_mul (le_abs_self _) p1 (by positivity) (abs_nonneg _))
        · exact q2.trans (mul_le_mul (le_abs_self _) p2 (by positivity) (abs_nonneg _))
    _ = (|C₁| + ‖c‖ * |C₂|) * H ^ (N₁ + N₂) := by ring

end GlobalTheory.ThK.GrowthDiff

end
