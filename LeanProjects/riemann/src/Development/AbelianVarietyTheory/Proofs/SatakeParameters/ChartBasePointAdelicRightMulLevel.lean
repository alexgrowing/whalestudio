import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.PtMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (κ : ((St i hi).K β).lev.U) (x x₁ : UA D i hi)
    (p q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (k : SB t μ → (Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i))),
    x₁.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → q.deco.1.N = p.deco.1.N → q.deco.1.f = p.deco.1.f →
    (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * k P) → (∀ P, k P ∈ GLint t.X.E (D.R.N i) P.1) →
    (∀ P, InFrame t.seam (A.fb i hi β) (t.cst μ).D P κ.1 (k P)) → IsPtAd A a i hi β x₁ q) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β κ x x₁ p q k hx hp hN hf hfr hk hin
  refine ⟨?_, ?_, ?_⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab x.1 κ.1 _ (hatStab_of_lev _ κ)]
  · intro P
    have e1 : ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P) =
        (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; group
    rw [e1, hfr P, map_mul (seamGL t.seam)]
    exact GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) (hin P) (GlobalTheory.CplPt.seamGL_int t.seam ⟨k P, hk P⟩)
  · intro P v h hv
    have H := GlobalTheory.CplPt.funMoved_mul_lev t.seam _ P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x.1) p.deco.1 κ (hp.fnl P v h hv)
    have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by rw [hx, mul_assoc]
    rw [e]
    intro w hw z hz
    have H2 := H w (hN ▸ hw) z hz
    rw [hf]
    exact H2

end GlobalTheory.PtMove

end
