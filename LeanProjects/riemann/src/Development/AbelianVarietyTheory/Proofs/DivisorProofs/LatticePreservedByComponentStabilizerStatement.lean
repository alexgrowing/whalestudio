import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservedByComponentStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_preserved_by_component_stabilizer : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp), ∀ γ ∈ ((uAt r v i).X k).Γ, ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ := by
  first | exact @GlobalTheory.ShareOn.sub_mem_half_smul_latP | exact GlobalTheory.ShareOn.sub_mem_half_smul_latP | (intros; apply GlobalTheory.ShareOn.sub_mem_half_smul_latP <;> assumption)
