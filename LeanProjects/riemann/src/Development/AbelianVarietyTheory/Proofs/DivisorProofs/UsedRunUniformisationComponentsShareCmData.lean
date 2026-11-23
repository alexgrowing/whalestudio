import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem comps_share : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ k k' : (uAt r v i).Comp, ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ ∧ ((uAt r v i).X k).p0 = ((uAt r v i).X k').p0 ∧ ((uAt r v i).X k).Gm = ((uAt r v i).X k').Gm ∧ ((uAt r v i).X k).ξ0 = ((uAt r v i).X k').ξ0 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k k'
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hL := (h.laws v).j
  have hg := (r.used v).full.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hg
  refine ⟨?_, ((hU.2.1 k).1.trans (hU.2.1 k').1.symm), ((hm k).1.trans (hm k').1.symm),
    ((hm k).2.trans (hm k').2.symm)⟩
  ext τ
  exact ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm

end GlobalTheory.ShareOn
