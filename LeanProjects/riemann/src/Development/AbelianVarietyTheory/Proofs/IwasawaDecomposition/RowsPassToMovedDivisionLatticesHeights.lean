import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReplacementValuesBaseLevelTypePartsEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedReadingSameMapsBaseReadingAgrees

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.DivMv

section Gen

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m}
  {R : RealDat3 a.D A3 Ks} {F : Face3 a.D A3} {X0 : BaseLevelRowSide a.D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)

def readB : letI := alg c.to iK; Read (A3 := famInThreeCoefficientChange c.to A3) (real3 c.to R).toRealDat (face3 c.to F).lv2 (baseLevelRowSideTransport c X0) :=
  (by with_unfolding_all exact ((Tr.read c Y) :))

theorem readB_tup : letI := alg c.to iK; HEq (readB c Y).tup Y.tup := (by with_unfolding_all exact ((HEq.refl Y.tup) :))

theorem readB_tupT : letI := alg c.to iK; HEq (readB c Y).tupT Y.tupT := (by with_unfolding_all exact ((HEq.refl Y.tupT) :))

theorem readB_PY : letI := alg c.to iK; HEq (readB c Y).PY.ψ Y.PY.ψ := (by with_unfolding_all exact ((HEq.refl Y.PY.ψ) :))

theorem readB_PW : letI := alg c.to iK; HEq (fun i => ((readB c Y).PW i).ψ) (fun i => (Y.PW i).ψ) := (by with_unfolding_all exact ((HEq.refl (fun i => (Y.PW i).ψ)) :))

theorem readB_eE : letI := alg c.to iK; HEq (readB c Y).eE Y.eE := (by with_unfolding_all exact ((HEq.refl Y.eE) :))

theorem readB_jA : letI := alg c.to iK; HEq (readB c Y).jA Y.jA := (by with_unfolding_all exact ((HEq.refl Y.jA) :))

theorem substitutedColumnValuesReading_baseCoordinatesA_eq : letI := alg c.to iK; HEq (readB c Y).jA0 Y.jA0 := (by with_unfolding_all exact ((HEq.refl Y.jA0) :))

theorem readB_eMt : letI := alg c.to iK; HEq (readB c Y).eMt Y.eMt := (by with_unfolding_all exact ((HEq.refl Y.eMt) :))

theorem readB_eW : letI := alg c.to iK; HEq (readB c Y).mj.eW Y.mj.eW := (by with_unfolding_all exact ((HEq.refl Y.mj.eW) :))

theorem readB_jE : letI := alg c.to iK; HEq (fun x => ((readB c Y).Ish.jE x).1) (fun x => (Y.Ish.jE x).1) :=
  (by with_unfolding_all exact ((heq_of_eq (funext fun x => val_trans_ofEq (j := Y.Ish.jE) (congrFun (spEEc_eq c F.lv2 Y.tupT Y.hm Y.hTop) true) x)) :))

theorem substitutedColumnValuesReading_baseLevelRows_eq : letI := alg c.to iK; HEq (fun x => ((readB c Y).Iz.jE x).1) (fun x => (Y.Iz.jE x).1) :=
  (by with_unfolding_all exact ((heq_of_eq (funext fun x => val_trans_ofEq (j := Y.Iz.jE) (congrFun (spEEc_eq c F.lv2 Y.tupT Y.hm Y.hTop) false) x)) :))

theorem readB_rep : letI := alg c.to iK
    HEq (fun π => principalLevelFrame.rowRepR (real3 c.to R).θ ((readB c Y).eFT π)) (fun π => principalLevelFrame.rowRepR R.θ (Y.eFT π)) :=
  (by with_unfolding_all exact ((heq_of_eq (funext fun π => (Tr.rep_eq c Y π).symm)) :))

variable {Y} (L : ReadL R F X0 Y)

theorem eRRu_heq (u : Parts R) : HEq (eRRu L u) L.eRR := (by with_unfolding_all exact ((HEq.refl L.eRR) :))

theorem eRR0u_heq (u : Parts R) : HEq (riemannRochSpaceCoordinateEquiv L u) L.eRR0 := (by with_unfolding_all exact ((HEq.refl L.eRR0) :))

def readLB : letI := alg c.to iK; ReadL (real3 c.to R) (face3 c.to F) (baseLevelRowSideTransport c X0) (readB c Y) := (by with_unfolding_all exact ((Tr.readL c L) :))

theorem readLB_jW : letI := alg c.to iK; HEq (readLB c L).jW L.jW := (by with_unfolding_all exact ((HEq.refl L.jW) :))

theorem readLB_eRR : letI := alg c.to iK; HEq (readLB c L).eRR L.eRR := (by with_unfolding_all exact ((eRRu_heq L (partsB c R)) :))

theorem substitutedColumnValuesLift_baseRowLatticeCoords_eq : letI := alg c.to iK; HEq (readLB c L).eRR0 L.eRR0 := (by with_unfolding_all exact ((eRR0u_heq L (partsB c R)) :))

end Gen

section Main

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0)

set_option maxHeartbeats 800000 in

def readMv : Read (datMv N h t.r.z).R.toRealDat (datMv N h t.r.z).F.lv2 ((p0Mv N h p0)) :=
  (by with_unfolding_all exact ((readB (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))

set_option maxHeartbeats 800000 in

def readLMv : ReadL (datMv N h t.r.z).R (datMv N h t.r.z).F ((p0Mv N h p0)) (readMv N h t) :=
  (by with_unfolding_all exact ((readLB (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Z) :))

set_option maxHeartbeats 1600000 in

theorem readSame : ReadSame N h t (readMv N h t) (readLMv N h t) where
  tup := (by with_unfolding_all exact ((readB_tup (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  tupT := (by with_unfolding_all exact ((readB_tupT (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  PY := (by with_unfolding_all exact ((readB_PY (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  PW := (by with_unfolding_all exact ((readB_PW (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  rep := (by with_unfolding_all exact ((readB_rep (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  jE := (by with_unfolding_all exact ((readB_jE (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  heq_eigen_embedding_zero := (by with_unfolding_all exact ((substitutedColumnValuesReading_baseLevelRows_eq (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  eE := (by with_unfolding_all exact ((readB_eE (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  jA := (by with_unfolding_all exact ((readB_jA (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  jA0 := (by with_unfolding_all exact ((substitutedColumnValuesReading_baseCoordinatesA_eq (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  eMt := (by with_unfolding_all exact ((readB_eMt (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  eW := (by with_unfolding_all exact ((readB_eW (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Y) :))
  jW := (by with_unfolding_all exact ((readLB_jW (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Z) :))
  eRR := (by with_unfolding_all exact ((readLB_eRR (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Z) :))
  eRR0 := (by with_unfolding_all exact ((substitutedColumnValuesLift_baseRowLatticeCoords_eq (a := Z) (Refill.ofDiv Z N h) (iK := t.r.z.alg) t.r.Z) :))

end Main

theorem rows_move : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h →
    ∃ t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0, RowsSame t t' ∧ HEq (SRe.pkOf t') ((SRe.pkOf t).up Z Z.S N h) ∧
      (ObjT O t → ObjT O' t') ∧ (Nonempty (RXs t) → Nonempty (RXs t')) :=
  fun K B f T w Z Wt O t N h O' hO => rows_move_of_read K B f T w Z Wt O t N h O' hO ⟨_, _, readSame N h t⟩

set_option maxHeartbeats 800000 in

theorem datMv_geo {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {hX : B.fields.Ok} (z : Dat (w.st Z) w.I hX T Wt) :
    HEq (datMv N h z).geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z Z.S N h) (iK := z.alg) z.geo) :=
  (by with_unfolding_all exact ((HEq.refl (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z Z.S N h) (iK := z.alg) z.geo)) :))

set_option maxHeartbeats 4000000 in

theorem rows_move_geo : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h →
    ∃ t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0, RowsSame t t' ∧
      HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z Z.S N h) (iK := t.r.z.alg) t.r.z.geo) ∧
      HEq (SRe.pkOf t') ((SRe.pkOf t).up Z Z.S N h) ∧ (ObjT O t → ObjT O' t') ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt O t N h O' hO
  subst hO
  have s := readSame N h t
  exact ⟨(by with_unfolding_all exact (s.what₂ :)), (by with_unfolding_all exact (s.rowsSame :)), (by with_unfolding_all exact ((datMv_geo N h t.r.z) :)), (by with_unfolding_all exact (s.pk :)), fun H => (by with_unfolding_all exact ((s.objT H) :)), fun ⟨x⟩ => ⟨(by with_unfolding_all exact ((s.rxs x) :))⟩⟩

end GlobalTheory.Mem.R3.Rw.DivMv

end
