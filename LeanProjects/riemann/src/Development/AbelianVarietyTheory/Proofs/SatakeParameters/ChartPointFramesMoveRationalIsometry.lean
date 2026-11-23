import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatFrame

set_option maxHeartbeats 400000 in

theorem frame_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
        (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i hi β x x₁ γ hγ h₁ g hg p hp P
  have hx : ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P) =
      ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) := by
    rw [h₁, hg, map_mul, map_mul, map_inv]
    group
  rw [hx]
  have h0 := hp.frame P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
    have hq := GlobalTheory.TopStep.qOf_notMem_sq hPin.fields.ok t.pr_ok hP
    have e1 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dif_pos hP]
    have h1 : NearAt (seamP t.seam P.1) 1 (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (p.deco.1.liftFr ⟨P.1, hP⟩)) := by
      rw [← e1, ← hD]; exact h0
    have e2 : frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs ×
        GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P =
        (((g, (1 : GLG t.X.E (D.R.N i) t.Pr.vGs)) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs) • p.deco).1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dif_pos hP]
      rfl
    have key := GlobalTheory.FrameRat.nearAt_liftFr_smul t.seam p.deco ⟨P.1, hP⟩ g hq _ h1
    rw [e2, hD]
    exact key
  · have e : frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs ×
        GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
      unfold frsF
      rw [dif_neg hP, dif_neg hP]
      show g.1 * _ * _ = _
      simp
      rfl
    rw [e, map_mul, nearAt_rat_mul]
    exact h0

end GlobalTheory.RatFrame

end
