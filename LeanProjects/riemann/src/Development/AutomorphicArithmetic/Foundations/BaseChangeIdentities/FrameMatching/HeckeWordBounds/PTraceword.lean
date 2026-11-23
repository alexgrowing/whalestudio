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

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.traceword_pf :
    U.UWord → LocMatch → ChainSc → FBL.EllHom → AdelWord → ArchSc → USph → UOk → FrFacts → TraceWord := by
  intro hUW hLM hCS hEH hAW hAS hUS hUO hFF hR E _ _ _ n π S T F₀ F hE hF ws hws
  obtain ⟨hμ, hnorm, hgood, hP⟩ := hFF hR E n π S T F₀ F
  obtain ⟨hcnt, hsph⟩ := hUS hR E n π S T F₀ F ws
  have hk : 1 ≤ ws.length := List.length_pos_iff.2 hws
  obtain ⟨hHecke, hsep, hall⟩ := hLM E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne hnorm hgood (lw F ws) F.m ws.length
    F.m_pos hk hcnt (ws.flatten.map (ul F)) (fun w _ => hsph w)
  have hlU : ∀ x ∈ ws.flatten.map (ul F), U.UGen.Ok F₀.Sec F.d.B x := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact (hUO hR E n π S T F₀ F hE p).1
  obtain ⟨hT, htr⟩ := hUW E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff hHecke ws.length _ hlU
  rw [htr hsep]
  have hch := hCS E n F₀.μ F₀.e F₀.lam F₀.C F₀.Sec F₀.hSec F.d.KU _ F.levOff.2.1 hT F₀.u₁ F₀.u₂ F₀.hu
    (fun a => (prodL F.d (lw F ws) a).tr F.d.P F.d.one) (fun a => (prodL F.d (lw F ws) a).t)
    (fun a ha => by
      obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hall a ha
      refine ⟨h1, h2, h3, fun w hw => ?_⟩
      rw [← hμ w]
      exact h4 w hw)
    (fun i => by
      obtain ⟨-, w, hw, hns, hreg⟩ := hall (F₀.C.a i) (F₀.C.le i)
      refine ⟨w, hw, ?_⟩
      have : seen ((prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one) (prodL F.d (lw F ws) (F₀.C.a i)).t w =
          (prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one w := by
        funext y
        simp [seen, hns]
      rw [this]
      exact hreg)
    (fun i v => (tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v))
    (fun i => (tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb)
    (fun i v => ((hAW hR E n π S T F₀ F hF i ws).2.2 v))
    (fun i => BGen.sc (ws.map (bw F i)).flatten) (U.UGen.sc (ws.flatten.map (ul F)))
    (fun i => by
      rw [Finset.prod_mul_distrib]
      exact hAS hR E n π S T F₀ F hF i ws)
  rw [hch]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, h2, -⟩ := hAW hR E n π S T F₀ F hF i ws
  rw [h1, hEH]
  field_simp

end
