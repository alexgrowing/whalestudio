import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDatum_levelPrime_invariant_mul_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi)
    (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
      ∀ z, phiT t.X.K p₁.deco.1 p₁'.deco.1 z = phiT t.X.K p.deco.1 p'.deco.1 z) := by
  first | exact @GlobalTheory.TwV.PhiTLev.phiT_mul_lev | exact GlobalTheory.TwV.PhiTLev.phiT_mul_lev | (intros; apply GlobalTheory.TwV.PhiTLev.phiT_mul_lev <;> assumption)
