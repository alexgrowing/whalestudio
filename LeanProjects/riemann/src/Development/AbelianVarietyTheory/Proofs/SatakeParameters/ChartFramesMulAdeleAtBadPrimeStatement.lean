import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrames_mul_adele_at_badPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameMove.frames_mul | exact GlobalTheory.FrameMove.frames_mul | (intros; apply GlobalTheory.FrameMove.frames_mul <;> assumption)
