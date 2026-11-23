import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.DatCopy

namespace GlobalTheory.Mem.R3.LiftCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} {R : RealDat3 a.D A Ks} {F : Face3 a.D A}

theorem holdsL_tr (h : HoldsL R F) : letI := alg b iK; HoldsL (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case heckeR => exact (by with_unfolding_all exact (h.heckeR :))
  case heckeL => exact (by with_unfolding_all exact (h.heckeL :))
  case hecke => tr_via (fun X : Cx.CxData A.fam3.amb3 => (∃ hE, Cx.HeckeIntertwiningDefinite A X hE) ∧ ∃ hW, Cx.HeckeIntertwiningLifts A X hW) (toCx3_eq b R F) h.hecke
  case gUnit => exact (by with_unfolding_all exact (h.gUnit :))
  case gEquiv => tr_via (fun u : Parts R => Cx.GEquiv3 A (cxW R F u) ((by with_unfolding_all exact ((R.gEx F) :))) ∧ Cx.LiftGroupEquivariance A (cxW R F u) ((by with_unfolding_all exact ((R.gWx F) :)))) (parts_eq b R F) h.gEquiv
  case block => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.zs.InBlock) (toCx3_eq b R F) h.block
  case liftTest => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTest X) (toCx3_eq b R F) h.liftTest
  case liftTestB => tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTestB X false) (toCx3_eq b R F) h.liftTestB
  case liftOnto => tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ hW, Cx.HeckeIntertwiningLifts A X hW →
      U2.OntoC A X F.P0 F.ψ0 F.P1 F.ψ1 hW) (toCx3_eq b R F) h.liftOnto
  case unif => exact (by with_unfolding_all exact (h.unif :))
  case mLat => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.MLat false) (toCx3_eq b R F) h.mLat
  case levW => tr_via (fun u : Parts R =>
      Cx.LevelTypeOfLifts A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) ((by with_unfolding_all exact ((R.gWx F) :))) false F.P0 F.ψ0) (parts_eq b R F) h.levW
  case thmA => tr_via (fun W : type_of% R.Wp3 => ∀ i t,
      Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (W i) fun p => R.lam3 i t p A.A.v0) (wp3_apply_eq_sq_mul_sub_sq_mul b R) h.thmA
  case sumW => tr_via (fun X : Cx.CxData A.fam3.amb3 => X.PartsW false) (toCx3_eq b R F) h.sumW
  case aux => exact (by with_unfolding_all exact ((realAdelicInertTransport_furtherRows b h.aux) :))
  case ok => exact (by with_unfolding_all exact (h.ok :))
  case sep => exact (by with_unfolding_all exact (h.sep :))

theorem holdsL_back (h : letI := alg b iK; HoldsL (real3 b R) (face3 b F)) : HoldsL R F := by
  have h2 := holdsL_tr (a := b) a (iK := alg b iK) h
  exact (by with_unfolding_all exact ((cast (congrArg (fun R' : RealDat3 a.D A Ks => HoldsL R' F) (twice_eq b R).symm) ((h2))) : _))

end Three

section Dat

variable {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {Tw : Top.TwDat B} {Wt : Set B.places.Pl}
  (s : SameGrp a b) {z : Dat a.st I hX Tw Wt}

theorem holdsL_of_copy (h : HoldsL (copy b s z).R (copy b s z).F) : HoldsL z.R z.F := holdsL_back b (iK := z.alg) ((by with_unfolding_all exact (h :)))

end Dat

end GlobalTheory.Mem.R3.LiftCopy

end
