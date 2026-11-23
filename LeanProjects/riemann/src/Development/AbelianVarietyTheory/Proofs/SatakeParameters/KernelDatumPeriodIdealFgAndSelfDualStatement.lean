import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) := by
  first | exact @GlobalTheory.TieLat.tie_AA_fg_and_sd | exact GlobalTheory.TieLat.tie_AA_fg_and_sd | (intros; apply GlobalTheory.TieLat.tie_AA_fg_and_sd <;> assumption)
