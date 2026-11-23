import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePointStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColSpanMapMulVecLin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem Joint.locSp_kerN_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD La hLa v
  obtain ⟨-, -, hK, -⟩ := hD 0 (Nat.zero_le _) La hLa
  rw [(J.lev0 _).1] at hK
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) := (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hT0 : 0 < (D.mem u).A.T := by
    rcases Nat.eq_zero_or_pos (D.mem u).A.T with h | h
    · rw [h, Nat.coprime_zero_left] at hcop
      exact absurd hcop (Fact.out : (D.what₂.places.resChar w).Prime).one_lt.ne'
    · exact h
  have hU := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have ho := GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (J.pins.crd_orth 0 (Nat.zero_le _))
  have hs := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint (J.Gd.forms u).cls0.lev (lev0At J.Gd u w hg).A J.a ⟨_, ho⟩ J.alg0 J.one.int J.lb0 hT0 La.1 _
    (J.pt std 0 (Nat.zero_le _) La) (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).2 v hU
  rw [GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa v]
  exact locSp_reindex (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ _ (lev0At J.Gd u w hg).A.rk _ _ _ _ _ hK hs

end GlobalTheory.TwV
