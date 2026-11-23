import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNearAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeamGLInjective
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_glint_nearAt {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : ℕ)
    (k : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hk : CongAt (seamP s P) 0 k) (hk' : CongAt (seamP s P) 0 k⁻¹) :
    ∃ g : GLint X.E n P, NearAt (seamP s P) d k (seamGL s g.1) := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.TwU.Approx.exists_nearAt D.host.F D.host.E n (d + 1) (seamP s P) k
  set h := seamLE s g0 with hhdef
  have hh : seamGL s h = g0 := seamGL_seamLE s g0
  have hC : CongAt (F := D.host.F) (seamP s P) (d + 1) (k⁻¹ * ratA D.host.F (seamGL s h)) := by
    rw [hh]; exact hg0
  have h0 : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h)) := by
    have e : ratA D.host.F (seamGL s h) = k * (k⁻¹ * ratA D.host.F (seamGL s h)) := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 hk (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _) hC)
  have h0' : CongAt (F := D.host.F) (seamP s P) 0 (ratA D.host.F (seamGL s h⁻¹)) := by
    rw [map_inv, map_inv]
    have e : (ratA D.host.F (seamGL s h))⁻¹ = (k⁻¹ * ratA D.host.F (seamGL s h))⁻¹ * k⁻¹ := by group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 0 (GlobalTheory.FrameMove.congAt_mono (Nat.zero_le _)
      (GlobalTheory.LevFrame.congAt_inv _ _ _ _ _ _ (Nat.succ_pos d) hC)) hk'
  have l1 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h h0
  have l2 := GlobalTheory.TwU.MidIndep.congAt_local s P 0 n h⁻¹ h0'
  have hmem : h ∈ GLint X.E n P := by
    refine fun w => ⟨fun hw => ?_, fun hw => GlobalTheory.FrameMove.mem_of_local P 0 h l1 w hw⟩
    have := GlobalTheory.FrameMove.mem_of_local P 0 h⁻¹ l2 _ hw
    rwa [show (h⁻¹ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (h w) = w from h.symm_apply_apply w] at this
  refine ⟨⟨h, hmem⟩, ?_⟩
  show CongAt _ d (k⁻¹ * ratA D.host.F (seamGL s h))
  exact GlobalTheory.FrameMove.congAt_mono (Nat.le_succ d) hC

end GlobalTheory.FrameShift

namespace GlobalTheory.FrameShift

theorem exists_pt_mul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i p y k hk hy
  choose g hg using fun P : SB t μ => exists_glint_nearAt t.seam P.1 ((t.cst μ).D P) (k P) (hk P).1 (hk P).2
  obtain ⟨q, κ, hN, hf, hfr, hκ⟩ := GlobalTheory.CplPt.exists_pt_frames p g
  refine ⟨q, hN, hf, fun P => ?_⟩
  have base := GlobalTheory.CplPt.nearAt_mul_int _ (hy P) (hg P) (GlobalTheory.CplPt.seamGL_int t.seam (g P))
  rw [hfr P, map_mul]
  by_cases hP : P.1 ∈ t.Pr.vGs
  · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
    have hq := (GlobalTheory.ColPeriod.levelPrimes t.X t.Pr t.sel t.S (t.tup μ) hPin.fields.ok t.pr_ok hPin.sel P).1.2
    have e : ((κ P)⁻¹).1 = (g P).1 * ((g P)⁻¹ * (κ P)⁻¹).1 := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [e, map_mul, ← mul_assoc]
    refine GlobalTheory.CplPt.nearAt_mul _ base ?_
    rw [hD]
    exact GlobalTheory.CplPt.congAt_one_of_redGL t.seam hq ((g P)⁻¹ * (κ P)⁻¹) (hκ P).1
  · rw [(hκ P).2 hP]
    exact base

end GlobalTheory.FrameShift
