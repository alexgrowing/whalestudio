import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.ExistsNotEisContinues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergenStatement

noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.AutomorphicL2Unitary
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled.Tr

theorem posSum_growth' (D : D7) (V : HSp D) (hV : 0 < V.rank) (a : GL (Fin V.rank) (AE D)) (ha : IsMaj V a)
    (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) (p : GA D (dblSp V)) (c : ℝ≥0) (hc : 0 < c)
    (h : GA D (dblSp V) → ℝ) (hh : ∀ x, h x = Real.log (hgt V a (x * p⁻¹)) + Real.log c) (t : ℝ)
    (ht : (V.rank : ℝ) < t) : ∃ (C : ℝ) (N : ℕ), ∀ g,
      ‖GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => (Real.exp (t * h x) : ℂ)) g‖ ≤
        C * GlobalTheory.Grow.height (dblSp V) g ^ N := by
  have hσ : (V.rank : ℝ) / 2 < t - (V.rank : ℝ) / 2 := by linarith
  obtain ⟨C₀, A, hC₀⟩ := GlobalTheory.T.sphericalSiegelEisenstein_moderate_growth_convergent D V hV a ha hI (t - (V.rank : ℝ) / 2) hσ
  have hpos : ∀ y, 0 < hgt V a y := fun y => hgtH_pos _
  have hf : (fun x => (Real.exp (t * h x) : ℂ)) = (Real.exp (t * Real.log c) : ℂ) •
      fun x => GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ) (x * p⁻¹) := by
    funext x
    have e : (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ) + (V.rank : ℂ) / 2 = (t : ℂ) := by push_cast; ring
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.Eis.sph]
    rw [npow_eq_exp (hpos _), e, hh x, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  refine ⟨Real.exp (t * Real.log c) * |C₀| * GlobalTheory.Grow.height (dblSp V) p⁻¹ ^ A, A, fun g => ?_⟩
  rw [hf, GlobalTheory.Eis.cosetSum_smul, GlobalTheory.Eis.cosetSum_mul_right, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have h1 := hC₀ (g * p⁻¹)
  have h2 : GlobalTheory.Grow.height (dblSp V) (g * p⁻¹) ^ A ≤
      (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A :=
    pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le (GlobalTheory.Grow.height_mul_le _ _ _) A
  have h3 : 0 ≤ GlobalTheory.Grow.height (dblSp V) (g * p⁻¹) ^ A := pow_nonneg (GlobalTheory.Grow.height_pos _ _).le A
  have h4 : ‖GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ)) (g * p⁻¹)‖ ≤
      |C₀| * (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C₀) h3).trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
  calc Real.exp (t * Real.log c) * ‖GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V))
        (GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ)) (g * p⁻¹)‖
      ≤ Real.exp (t * Real.log c) * (|C₀| * (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = Real.exp (t * Real.log c) * |C₀| * GlobalTheory.Grow.height (dblSp V) p⁻¹ ^ A * GlobalTheory.Grow.height (dblSp V) g ^ A := by
        rw [mul_pow]; ring

end ResidueKilled.Tr
