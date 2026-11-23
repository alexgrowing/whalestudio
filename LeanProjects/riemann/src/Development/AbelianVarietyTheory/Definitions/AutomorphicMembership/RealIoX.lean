import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def real {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @RealDat b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) :=
  @RealDat.mk b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK)
    (toLevCh := levCh b R.toLevCh)
    (hv0 := (by with_unfolding_all exact (R.hv0 :)))
    (eG := (by with_unfolding_all exact (R.eG :)))
    (pl := (by with_unfolding_all exact (R.pl :)))
    (Sb := (by with_unfolding_all exact (R.Sb :)))
    (θ := (by with_unfolding_all exact (R.θ :)))
    (ψ := (by with_unfolding_all exact (R.ψ :)))
    (MY := fun j => (by with_unfolding_all exact ((ds b (R.MY j)) :)))
    (MX := (by with_unfolding_all exact ((ds b R.MX) :)))
    (MW := fun i σ => (by with_unfolding_all exact ((ds b (R.MW ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (σ :))))) :)))
    (cX := (by with_unfolding_all exact ((coefA b R.cX) :)))
    (cV := fun i => (by with_unfolding_all exact ((coefA b (R.cV ((by with_unfolding_all exact (i :))))) :)))
    (B := (by with_unfolding_all exact ((famReal b R.B) :)))
    (prX := (by with_unfolding_all exact (R.prX :)))
    (HX := (by with_unfolding_all exact (R.HX :)))
    (HV := (by with_unfolding_all exact (R.HV :)))
    (HE := (by with_unfolding_all exact (R.HE :)))
    (HW := (by with_unfolding_all exact (R.HW :)))
    (gE := (by with_unfolding_all exact (R.gE :)))
    (gW := (by with_unfolding_all exact (R.gW :)))
    (jX := (by with_unfolding_all exact (R.jX :)))
    (jV := (by with_unfolding_all exact (R.jV :)))
    (νY := (by with_unfolding_all exact (R.νY :)))
    (fdY := (by with_unfolding_all exact (R.fdY :)))
    (ν0 := (by with_unfolding_all exact (R.ν0 :)))
    (fd0 := (by with_unfolding_all exact (R.fd0 :)))
    (νX := (by with_unfolding_all exact (R.νX :)))
    (fdX := (by with_unfolding_all exact (R.fdX :)))
    (νV := (by with_unfolding_all exact (R.νV :)))
    (fdV := (by with_unfolding_all exact (R.fdV :)))
    (νW := (by with_unfolding_all exact (R.νW :)))
    (fdW := (by with_unfolding_all exact (R.fdW :)))
    (ωY := (by with_unfolding_all exact (R.ωY :)))
    (ωX := (by with_unfolding_all exact (R.ωX :)))
    (ωP := (by with_unfolding_all exact (R.ωP :)))
    (vac := (by with_unfolding_all exact (R.vac :)))
    (vacX := (by with_unfolding_all exact (R.vacX :)))
    (vacP := (by with_unfolding_all exact (R.vacP :)))
    (vY := (by with_unfolding_all exact (R.vY :)))
    (vX := (by with_unfolding_all exact (R.vX :)))
    (vP := (by with_unfolding_all exact (R.vP :)))
    (ItY := (by with_unfolding_all exact (R.ItY :)))
    (ItX := (by with_unfolding_all exact (R.ItX :)))
    (ioY := (by with_unfolding_all exact ((ioYB b R) :)))
    (ioX := (by with_unfolding_all exact ((ioXB b R) :)))
    (Th := (by with_unfolding_all exact (R.Th :)))
    (BV := (by with_unfolding_all exact (R.BV :)))
    (ioP := (by with_unfolding_all exact (R.ioP :)))
    (thF := (by with_unfolding_all exact (R.thF :)))
    (thG := (by with_unfolding_all exact (R.thG :)))
    (nW := (by with_unfolding_all exact (R.nW :)))
    (FW := (by with_unfolding_all exact (R.FW :)))
    (mu := (by with_unfolding_all exact (R.mu :)))
    (twPl := (by with_unfolding_all exact (R.twPl :)))
    (kap := (by with_unfolding_all exact (R.kap :)))
    (lam := (by with_unfolding_all exact (R.lam :)))
    (err0 := (by with_unfolding_all exact (R.err0 :)))

theorem real_ioY {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoYT (@MultT a.D) R) ((R.ioY)) _ (@RealDat.ioY b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoYT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioY :)))).2 :))

theorem real_ioX {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoXT (@MultT a.D) R) ((R.ioX)) _ (@RealDat.ioX b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoXT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioX :)))).2 :))

def real3 {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) :
    @RealDat3 b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) :=
  @RealDat3.mk b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) ((by with_unfolding_all exact ((real b R.toRealDat) :))) ((by with_unfolding_all exact (R.plI :))) ((by with_unfolding_all exact (R.SF :))) ((by with_unfolding_all exact (R.phs :)))
    ((by with_unfolding_all exact (R.lam3 :)))

scoped macro "tr_delta" : tactic => `(tactic|
  try
    delta
      RealDat.chain_vY RealDat.models_HE RealDat.thP_vP RealDat.cw_ItX RealDat.cw_ItY RealDat.chain_vX IsStepVecOf
      RealDat.models_HW RealDat.EEat RealDat.ex_ItX RealDat.ex_ItY RealDat3.full_P RealDat3.full_X
      WeilFull.RealAtO WeilFull.SphInertAtO RealDat3.full_Y RealDat3.in_tie RealDat.thP_pt_theta IsThPVecOf
      RealDat.thP_ωP RealDat.PItX RealDat.PItY RealDat.chain_ptX RealDat.chain_ptY IsThetaAt IsVacO
      RealDat.chain_ωX RealDat.chain_ωY RealDat.Wall Mult.goodPart RealDat.fam_tie)

scoped macro "tr_leaves " a:term:max b:term:max : tactic => `(tactic| (
      (try rewrite [mult_eq $a $b])
      (try rewrite [thetaFun_eq $a $b])
      (try rewrite [vacuum_eq $a $b])
      (try rewrite [placeModel_eq $a $b])
      (try rewrite [itW_eq $a $b])
      (try rewrite [pairSetup_eq $a $b])
      (try rewrite [inertTie_eq $a $b])
      (try rewrite [famTie_eq $a $b])
      (try rewrite [weilDatum_eq $a $b])
      (try rewrite [weilFull_eq $a $b])))

scoped macro "tr_clause " a:term:max b:term:max h:term:max : tactic => `(tactic| (tr_delta; tr_leaves $a $b; kexactB $h))

end GlobalTheory.Mem.R3.Tr

end
