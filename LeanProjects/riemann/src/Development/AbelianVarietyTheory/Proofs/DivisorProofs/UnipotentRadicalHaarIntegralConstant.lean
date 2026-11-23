import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinTransverseTermFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactRightTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesConvergesRightHalfStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisMidConv

theorem lintegral_midSet_lt_top : GlobalTheory.Published.EisensteinIsotropicLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 →
    ∀ s : ℝ, (n : ℝ) - 2 < s → ∀ g : GAd σ J,
    ∫⁻ u in 𝓕, ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h (t.1.1 * (u.1 * g)) ^ s) ∂μ < ⊤ := by
  intro hP F E _ _ _ _ _ σ n J r X Y L a h hS T hT μ 𝓕 _ _ h1 s hs g
  have hn : (4 : ℝ) ≤ n := by exact_mod_cast hS.2.2.2.1
  have hs0 : 0 ≤ s := by linarith
  have hpos : ∀ g, 0 ≤ h g := fun g => by
    obtain ⟨p, l, hp, k, hk, rfl⟩ := hS.2.2.2.2.2.2.1 g
    rw [hS.2.2.2.2.2.2.2 p l hp k hk]; exact NNReal.coe_nonneg _
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.T.unipotent_radical_rational_translate F E σ n J r X Y L a h hS
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.height_function_compact_right_translate F E σ n J r X Y L a h hS ((fun c => c * g) '' C) (hC.image (continuous_mul_right g))
  have hsum := GlobalTheory.T.eisenstein_series_converges_right_half hP F E σ n J r X Y L a h hS T hT s hs
  have hb : ∀ u : unipRad σ J (col0 X), ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h (t.1.1 * (u.1 * g)) ^ s) ≤
      ENNReal.ofReal (K ^ s) * ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h t.1.1 ^ s) := by
    intro u
    obtain ⟨ν, hνr, hνN, hνC⟩ := hcov u.1 u.2
    rw [← GlobalTheory.T.eisenstein_transverse_term_formula F E σ n J r X Y L a h hS T hT ν hνr hνN s (u.1 * g), ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun t => ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK0 s)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hK t.1.1 (ν * (u.1 * g)) ⟨ν * u.1, hνC, by simp [mul_assoc]⟩
    rw [← Real.mul_rpow hK0 (hpos _)]
    exact Real.rpow_le_rpow (hpos _) this hs0
  calc ∫⁻ u in 𝓕, ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h (t.1.1 * (u.1 * g)) ^ s) ∂μ
      ≤ ∫⁻ _ in 𝓕, ENNReal.ofReal (K ^ s) * ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h t.1.1 ^ s) ∂μ :=
        lintegral_mono fun u => hb u
    _ = _ := by rw [setLIntegral_const, h1, mul_one]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum

end GlobalTheory.EisMidConv
