import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (κ : ((St i hi).K β).lev.U),
    x₁.1 = x.1 * κ.1 → ∀ p p₁, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (dep : SB t μ → ℕ), dep P = 1 → ∀ (Gg : GLint t.X.E (D.R.N i) P.1),
      InFrame t.seam (A.fb i hi β) dep P κ.1 Gg.1 →
      ∃ k : GLint t.X.E (D.R.N i) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
        redGL _ P.1 k = redGL _ P.1 Gg) := by
  first | exact @GlobalTheory.LevFrame.frame_lev | exact GlobalTheory.LevFrame.frame_lev | (intros; apply GlobalTheory.LevFrame.frame_lev <;> assumption)
