import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La hLa
  obtain ⟨-, hA⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La
  have hb := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa
  obtain ⟨hγ, κ, hκ⟩ := pt00 J.one La.1 La.2 _ hb _ hA
  have hc : clsAt X H 0 La.1 La.2 = J.e0 (levelZeroClass J.one La.1 La.2) := J.cls0 La.1 La.2 hLa

  obtain ⟨κ', hκ'⟩ := (J.y0 (levelZeroClass J.one La.1 La.2)).imp fun _ h => h.1
  have hU := (J.lev0 (J.chart std 0 (Nat.zero_le _) La)).2.2.1
  have hm : κ'.1⁻¹ * κ.1 ∈ (J.Gd.forms u).cls0.lev.U := Subgroup.mul_mem _ (Subgroup.inv_mem _ κ'.2) κ.2
  refine ⟨rationalElementZero J.one La.1 La.2, hγ, ⟨κ'.1⁻¹ * κ.1, by rw [hU]; exact hm⟩, ?_⟩
  rw [hc, hκ', hκ]
  show _ = _ * _ * (κ'.1⁻¹ * κ.1)
  simp only [mul_assoc, mul_inv_cancel_left]
  rfl
