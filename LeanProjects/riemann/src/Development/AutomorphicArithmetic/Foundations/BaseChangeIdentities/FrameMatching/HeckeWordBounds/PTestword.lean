import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.testword_pf :
    PTTest → LocMatch → PsiWord → ProdOk → USph → TwOk → FrFacts → LocOk → TestWord := by
  intro hPT hLM hPsi hProd hSph hTw hFr hLoc hR E _ _ _ n π S T F₀ F hE hF i
  obtain ⟨c₀, hc₀, H⟩ := hPT E (F.B i)
  refine ⟨c₀, hc₀, fun ws hws => ?_⟩
  obtain ⟨-, hnorm, hgood, hP⟩ := hFr hR E n π S T F₀ F
  obtain ⟨hcount, hsph⟩ := hSph hR E n π S T F₀ F ws
  have hk : 1 ≤ ws.length := List.length_pos_iff.2 hws
  have hL := hLM E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne hnorm hgood (lw F ws) F.m ws.length
    F.m_pos hk hcount (ws.flatten.map (ul F)) (fun w _ => hsph w)
  have hle := F₀.C.le i
  have hreg := (hL.2.2 (F₀.C.a i) hle).2
  exact H F.d.kap F₀.Sec F.d.P (Equiv.refl _) F₀.hSec hP (fun w _ => (hLoc E n F.d F.ok _ hle).1 w)
    (F₀.u₁ _) (F₀.u₂ _) (F₀.hu _).1 (F₀.hu _).2 (F₀.A i).Ta (F₀.A i).Tb F.d.one (tw F i ws)
    (prodL F.d (lw F ws) (F₀.C.a i)) ⟨(F₀.A i).vca, (F₀.A i).vcb⟩ ((hTw hR E n π S T F₀ F hF i).2.2 ws)
    (hProd E n F.d F.ok _ _ hle) (hPsi hR E n π S T F₀ F i ws) hreg

end
