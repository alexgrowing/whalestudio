import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChartStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSuccStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePointStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColSpanMapMulVecLin
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.TwV.Joint.locSp_kerN_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa v
  obtain ⟨-, -, hker, -⟩ := hD (j + 1) hj La hLa
  obtain ⟨hTT, hLb, -⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  obtain ⟨-, hpt⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La
  have hbas := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa v
  rw [hLb] at hker
  have hcop : Nat.Coprime (I.at' j hj).st.T (D.what₂.places.resChar w) := by
    rw [hTT]
    exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  have hT0 : 0 < (I.at' j hj).st.T := by
    rcases Nat.eq_zero_or_pos (I.at' j hj).st.T with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop
      exact absurd hcop hp.one_lt.ne'
    · exact h0
  have hun := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have horth : ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (j + 1) hj) co :=
    ⟨_, GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ _ (J.pins.crd_orth (j + 1) hj)⟩
  have hK := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1) J.a horth (J.alg j hj _) (H.core j hj _).int (J.lbB j hj _) hT0
    _ _ (J.pt std (j + 1) hj La) hpt v hun
  have hR := @GlobalTheory.TwV.locSp_reindex _ _ _ (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (_) (_) (_) _ _ _
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk _ _ _ _ _ hker hK
  have hch := (dif_pos hj : chAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om I
    (lev0At J.Gd u w hg).A (lev0At J.Gd u w hg).J (lev0At J.Gd u w hg).Lb (lev0At J.Gd u w hg).Uloc (j + 1) La = _)
  have hJ := congrArg PtCh.J hch
  have hB := congrArg PtCh.B hch
  have hi := congrArg (fun c => PtCh.iw c v) hch
  have hfr : (J.fd std).frM (j + 1) La v = _ :=
    congrArg (fun M => Matrix.submatrix M (finCongr rfl) (finCongr rfl))
      (congr (congrArg Matrix.map (congr (congrArg HMul.hMul (congrArg (fun Q => LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) Q).toLinearMap) hJ))
        (congrArg Units.val hB))) (congrArg DFunLike.coe hi))
  rw [hfr, hbas]
  have hiw : J.rho std v = ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).iw v := (J.iw j hj _ v).symm
  rw [hiw]
  exact hR
