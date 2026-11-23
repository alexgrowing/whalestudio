import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAllFramesOfDenseOpenStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transp_all : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, h1⟩ := GlobalTheory.T.exists_transporter_moves_frame_reads_inverse p hp r h hr i v
  refine ⟨ψ, fun γ k => ?_⟩
  let V := Frame ((uAt r v i).X k).Ψ D.R.r
  let Dk : Set V := ((uAt r v i).X k).dom
  have hDo : IsOpen Dk := FourierCoefficientDomain.isOpen_dom _
  have hDn : Dk.Nonempty := (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
  let ι := Σ k' : (uAt r v i).Comp, {a : GL (Fin D.R.r) D.host.E //
    ∃ hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a, ReadsInv p r i v ψ γ k k' a}
  let S : ι → Set V := fun c => {x | ∃ hx : x ∈ Dk, MovesAt p r i v γ k c.1 c.2.1 c.2.2.1 x hx}
  haveI : Countable ι := inferInstance
  obtain ⟨x₀, hx₀⟩ := hDn
  haveI : Nonempty ι := by
    obtain ⟨k', a, hm, hR, -⟩ := h1 γ k x₀ hx₀
    exact ⟨⟨k', a, hm, hR⟩⟩
  haveI : Nonempty Dk := ⟨⟨x₀, hx₀⟩⟩
  haveI : LocallyCompactSpace Dk := hDo.locallyCompactSpace
  let T : ι → Set Dk := fun c => Subtype.val ⁻¹' closure (S c)
  have hTc : ∀ c, IsClosed (T c) := fun c => isClosed_closure.preimage continuous_subtype_val
  have hTu : ⋃ c, T c = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨k', a, hm, hR, hM⟩ := h1 γ k y.1 y.2
    exact Set.mem_iUnion.2 ⟨⟨k', a, hm, hR⟩, subset_closure ⟨y.2, hM⟩⟩
  obtain ⟨c, hc⟩ := nonempty_interior_of_iUnion_of_closed hTc hTu
  obtain ⟨k', a, hm, hR⟩ := c
  refine ⟨k', a, isTransp_of_movesAt hm ?_ hR⟩
  refine GlobalTheory.T.transporter_moves_all_frames_of_dense_open p hp r h hr i v γ k k' a hm (Subtype.val '' interior (T ⟨k', a, hm, hR⟩))
    (hDo.isOpenMap_subtype_val _ isOpen_interior) (hc.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ T ⟨k', a, hm, hR⟩ := interior_subset hy
    exact hy'

end GlobalTheory.ShareOn

end
