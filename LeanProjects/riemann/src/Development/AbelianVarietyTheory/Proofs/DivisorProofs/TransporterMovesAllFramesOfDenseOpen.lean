import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesNearbyFramesOfDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAtOfMovesAtOpenSetStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem movesAt_of_dense : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (O : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen O → O.Nonempty → O ⊆ ((uAt r v i).X k).dom → O ⊆ closure {x | ∃ hx : x ∈ ((uAt r v i).X k).dom, MovesAt p r i v γ k k' a hm x hx} → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k' a hm x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v γ k k' a hm O hO hOn hOd hOc x hx
  obtain ⟨o, ho⟩ := hOn
  obtain ⟨h1, k'', c, hc, hM⟩ := GlobalTheory.T.transporter_moves_nearby_frames_of_dense p hp r h hr i v γ k k' a hm o (hOd ho)
  obtain ⟨N, hN, hNM⟩ := h1 (Filter.mem_of_superset (hO.mem_nhds ho) hOc)
  exact GlobalTheory.T.transporter_movesAt_of_movesAt_open_set p hp r h hr i v γ k k' k'' a c hm hc (interior N ∩ O) (isOpen_interior.inter hO)
    ⟨o, mem_interior_iff_mem_nhds.2 hN, ho⟩ (fun w hw => hOd hw.2)
    (fun w hw hwW => ⟨hNM w hw (interior_subset hwW.1), hM w hw⟩) x hx (hM x hx)

end GlobalTheory.ShareOn

end
