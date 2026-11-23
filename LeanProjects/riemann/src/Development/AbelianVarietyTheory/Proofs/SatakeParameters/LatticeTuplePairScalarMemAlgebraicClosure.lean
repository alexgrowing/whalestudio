import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiDetIdAndChiFacAlg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSiteStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hj La La' hLa hLa'
  have hjm : j < D.R.m := lt_of_lt_of_eq hj X.fl_m
  have hj' : j + 1 ≤ D.R.m := hjm
  have hχ := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).1
  have h1 : S.muT (j + 1) ((J.fd std).dt j La) ∈ TaylorLogMetric.Qbar := by
    rw [(hD j hjm.le La hLa).2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D j hjm.le _)
  have h2 : S.muT (j + 1) ((J.fd std).dt (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    rw [(hD (j + 1) hj' La' hLa').2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D (j + 1) hj' _)
  have k1 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD j hjm.le La hLa
  have k2 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD (j + 1) hj' La' hLa'
  exact mul_mem (mul_mem (mul_mem h2 (inv_mem h1)) (zpow_mem (hχ _ _ k1.1 k1.2) _)) (zpow_mem (hχ _ _ k2.1 k2.2) _)
