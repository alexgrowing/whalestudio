import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siteSystem_ranks_eq_datum_ranks : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (sysS H X std).mm = D.R.m ∧ (sysS H X std).t = D.R.t ∧ (∀ j, ((sysS H X std).Pj j).m + 1 = D.R.N j) ∧ ∀ j, RankTie (sysS H X std) D j) := by
  first | exact @GlobalTheory.TwV.DelB.sysS_ranks | exact GlobalTheory.TwV.DelB.sysS_ranks | (intros; apply GlobalTheory.TwV.DelB.sysS_ranks <;> assumption)
