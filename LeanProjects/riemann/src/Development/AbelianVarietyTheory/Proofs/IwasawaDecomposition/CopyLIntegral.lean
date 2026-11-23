import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.DatCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def setIo (R : RealDat3 D A Ks) (y : type_of% R.ioY) (x : type_of% R.ioX) : RealDat3 D A Ks :=
  { R with ioY := y, ioX := x }

end Gen

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) {F : Face3 a.D A}

def twice : RealDat3 a.D A Ks := (by with_unfolding_all exact ((real3 (a := b) a (iK := alg b iK) (real3 b R)) :))

def twiceY : type_of% R.ioY := kc% (twice b R).ioY

def twiceX : type_of% R.ioX := kc% (twice b R).ioX

theorem twiceY_eq : R.ioY = twiceY b R :=
  eq_of_heq ((by with_unfolding_all exact ((HEq.trans (real_ioY b R.toRealDat) (kc% (real_ioY (a := b) a (iK := alg b iK) (real b R.toRealDat))) :
    HEq _ (twiceY b R)) :)))

theorem twiceX_eq : R.ioX = twiceX b R :=
  eq_of_heq ((by with_unfolding_all exact ((HEq.trans (real_ioX b R.toRealDat) (kc% (real_ioX (a := b) a (iK := alg b iK) (real b R.toRealDat))) :
    HEq _ (twiceX b R)) :)))

theorem twice_eq : R = twice b R := (by with_unfolding_all exact ((congrArg₂ (setIo R) (twiceY_eq b R) (twiceX_eq b R)) :))

variable {R}

theorem holds_back (h : letI := alg b iK; Holds (real3 b R) (face3 b F)) : Holds R F := by
  have h2 := holds_tr (a := b) a (iK := alg b iK) h
  exact (by with_unfolding_all exact ((cast (congrArg (fun R' : RealDat3 a.D A Ks => Holds R' F) (twice_eq b R).symm) ((h2))) : _))

theorem rowTest_tr (h : Rat.RowTest (R.toCx3 F)) : letI := alg b iK; Rat.RowTest ((real3 b R).toCx3 (face3 b F)) := by
  tr_via (fun X : Cx.CxData A.fam3.amb3 => Rat.RowTest X) (toCx3_eq b R F) h

end Three

theorem multEq_tr {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} (h : GlobalTheory.CuspMult.MultEq R) :
    letI := alg b iK; GlobalTheory.CuspMult.MultEq (real b R) := by
  intro i M₀ j Φ hI W _ _ σ h1 h2 h3
  have key := h ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact ((ds a M₀) :))) ((by with_unfolding_all exact (j :))) ((by with_unfolding_all exact (Φ :))) ⟨(by with_unfolding_all exact (hI.isom :)), (by with_unfolding_all exact (hI.conj :)), (by with_unfolding_all exact (hI.frame :))⟩ W ((by with_unfolding_all exact (σ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (h3 :)))
  delta GlobalTheory.CuspMult.cuspMult GlobalTheory.CuspMult.allMaps
  rewrite [mult_eq a b]
  exact (by with_unfolding_all exact (key :))

section Dat

variable {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {Tw : Top.TwDat B} {Wt : Set B.places.Pl}

set_option maxHeartbeats 2000000 in

def copy (s : SameGrp a b) (z : Dat a.st I hX Tw Wt) : Dat b.st I hX Tw Wt :=
  @Dat.mk b.st px I hX Tw Wt z.Xg z.tr (coreJ b z.core) ((by with_unfolding_all exact ((alg b z.alg) :))) ((by with_unfolding_all exact (z.alg_eq :))) ((by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :)))
    ((by with_unfolding_all exact ((z.cG.trans s.iso) :))) ((by with_unfolding_all exact ((geoHalf b (iK := z.alg) z.geo) :))) ((by with_unfolding_all exact ((pins_tr b (iK := z.alg) s z.pins) :)))
    ⟨(by with_unfolding_all exact ((levIs_tr b z.lev.is) :)), (by with_unfolding_all exact ((congrArg (chFr b) z.lev.C) :)), (by with_unfolding_all exact (z.lev.xiH :)), (by with_unfolding_all exact (z.lev.Pg :)), (by with_unfolding_all exact (z.lev.Q :)), (by with_unfolding_all exact (z.lev.beta :))⟩
    ((by with_unfolding_all exact (z.idG :)))
    (by
      have h := (goodSet_iff a.st (px := px) _ _).1 z.good
      have e : ∀ g, a.D.ntypes.e0.coeff ((z.R.eG.trans z.cG) g) = b.D.ntypes.e0.coeff (((z.R.eG.trans z.cG).trans s.iso) g) :=
        fun g => (s.e0 _).symm
      simp only [e] at h
      exact (by with_unfolding_all exact (((goodSet_iff b.st (px := px) ((z.R.eG.trans z.cG).trans s.iso) z.Xg).2 h) :)))
    ((by with_unfolding_all exact (z.mu :))) ((by with_unfolding_all exact (z.fieldValues_mem_fixedField :))) ((by with_unfolding_all exact (z.Ks_le :)))

variable (s : SameGrp a b) {z : Dat a.st I hX Tw Wt}

theorem copy_exAt (h : z.R.toRealDat.ExAt) : (copy b s z).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr b (iK := z.alg) h) :))

theorem copy_lUnif (h : z.R.toRealDat.LUnif) : (copy b s z).R.toRealDat.LUnif := (by with_unfolding_all exact (h :))

theorem copy_lIntegral (h : z.R.toRealDat.LIntegral) : (copy b s z).R.toRealDat.LIntegral := (by with_unfolding_all exact (h :))

theorem copy_multEq (h : GlobalTheory.CuspMult.MultEq z.R.toRealDat) : GlobalTheory.CuspMult.MultEq (copy b s z).R.toRealDat :=
  (by with_unfolding_all exact ((multEq_tr b (iK := z.alg) h) :))

theorem copy_rowTest (h : Rat.RowTest (z.R.toCx3 z.F)) : Rat.RowTest ((copy b s z).R.toCx3 (copy b s z).F) :=
  (by with_unfolding_all exact ((rowTest_tr b (iK := z.alg) h) :))

theorem holds_of_copy (h : Holds (copy b s z).R (copy b s z).F) : Holds z.R z.F := holds_back b (iK := z.alg) ((by with_unfolding_all exact (h :)))

end Dat

end GlobalTheory.Mem.R3.DatCopy

end
