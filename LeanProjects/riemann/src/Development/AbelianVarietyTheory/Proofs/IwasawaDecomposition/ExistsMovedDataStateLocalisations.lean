import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Fin3.MvLoc

section Three

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A : DIV.FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} (R : Links.RealDat3 a.D A Ks)

def thrice : type_of% (real3 c R) := (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thriceY : type_of% (letI := alg c iK; (real3 c R).ioY) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioY :))

def thriceX : type_of% (letI := alg c iK; (real3 c R).ioX) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioX :))

theorem thriceY_eq : letI := alg c iK; (real3 c R).ioY = thriceY b c R := by
  have h1 := real_ioY c R.toRealDat
  have h2 := real_ioY b R.toRealDat
  have h3 := real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceY b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thriceX_eq : letI := alg c iK; (real3 c R).ioX = thriceX b c R := by
  have h1 := real_ioX c R.toRealDat
  have h2 := real_ioX b R.toRealDat
  have h3 := real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceX b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thrice_eq : real3 c R = thrice b c R := by
  letI := alg c iK
  exact (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (real3 c R)) (thriceY_eq b c R) (thriceX_eq b c R)) :))

theorem inertTransport_twice_heq_direct : HEq (real3 (a := b) c (iK := alg b iK) (real3 b R)) (real3 c R) :=
  (by with_unfolding_all exact ((HEq.symm (heq_of_eq (thrice_eq b c R))) :))

end Three

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

theorem coreJ_heq {k₀ : Formalism.L2.Pj.CoreJ a.D} {k : Formalism.L2.Pj.CoreJ b.D} (h : HEq k (coreJ b k₀)) : HEq (coreJ c k) (coreJ c k₀) := by
  obtain rfl : k = coreJ b k₀ := eq_of_heq h
  exact (by with_unfolding_all exact ((HEq.refl (coreJ c k₀)) :))

theorem realAdelicInertTransport_heq_of_transport (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px) (k : Formalism.L2.Pj.CoreJ b.D)
    (i : Algebra k.Q.c.F b.D.what₂.LL) (hi : ∀ y : k.Q.c.F, B.embLL (algebraMap k.Q.c.F b.D.what₂.LL y) = (y : ℂ))
    (R : Links.RealDat3 b.D (famR b.st I hX (usedOf I T Wt) Xg tr) k.Q.c.F) (hXg : Xg = z₀.Xg)
    (htr : tr = z₀.tr) (hc : HEq k (coreJ b z₀.core)) (hR : HEq R (real3 b (iK := z₀.alg) z₀.R)) :
    HEq (real3 c (iK := i) R) (real3 c (iK := z₀.alg) z₀.R) := by
  subst hXg htr
  obtain rfl : k = coreJ b z₀.core := eq_of_heq hc
  have ha : i = (by with_unfolding_all exact ((alg b z₀.alg) :)) :=
    Algebra.algebra_ext _ _ fun y => (by with_unfolding_all exact ((B.embLL.injective ((hi y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))) :
      _ = (@algebraMap _ _ _ _ z₀.alg ((by with_unfolding_all exact (y :))) : B.LL)) :))
  subst ha
  have hR' : R = (by with_unfolding_all exact ((real3 b (iK := z₀.alg) z₀.R) :)) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  exact (by with_unfolding_all exact ((inertTransport_twice_heq_direct b c (iK := z₀.alg) z₀.R) :))

end Copy

section Move

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o o' : q.Over}

theorem coreP_transfer {Z Z' : w.Lt} (s : SameGrp (B := B) (C := w.C) Z Z') {z : Dat (w.st Z) w.I hX T Wt} (h : CoreP z) :
    CoreP (w := w) (Z := Z') (Dat.transfer (B := B) (C := w.C) (a := Z) (b := Z') s z) :=
  ⟨(by with_unfolding_all exact ((Mv.lawsCore_tr (a := Z) Z' h.1) :)), (by with_unfolding_all exact (h.2.1 :)), (by with_unfolding_all exact (h.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2 :))⟩

theorem copy_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) {m : Moved o} {m' : Moved o'} (hm : m.Copy)
    (e : m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z) : m'.Copy := by
  have h1 := coreJ_heq (a := Z₀) o.Z o'.Z (k₀ := z₀.core) (k := m.z.core) ((by with_unfolding_all exact (hm.core :)))
  have h2 := realAdelicInertTransport_heq_of_transport (a := Z₀) o.Z o'.Z z₀ m.z.Xg m.z.tr m.z.core m.z.alg m.z.alg_eq m.z.R m.Xg m.tr ((by with_unfolding_all exact (hm.core :))) ((by with_unfolding_all exact (hm.R :)))
  have e1 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.core) e
  have e2 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.R) e
  have h3 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).core (coreJ (a := Z₀) o'.Z z₀.core) := (by with_unfolding_all exact (h1 :))
  have h4 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).R (real3 (a := Z₀) o'.Z (iK := z₀.alg) z₀.R) := (by with_unfolding_all exact (h2 :))
  exact ⟨(by with_unfolding_all exact ((HEq.trans e1 h3) :)), (by with_unfolding_all exact ((HEq.trans e2 h4) :))⟩

theorem exists_moved_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hm : m.Coh) :
    ∃ m' : Moved o', m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := Mv.pkT_tr (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  have hW := Dat.nonzeroIndexPlaces_transferAlongSameFiniteGroup (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have b2 := HEq.trans hy.PY hm.PY
  have b3 := HEq.trans hy.PW hm.PW
  have b4 := HEq.trans a2 hm.rep
  have b5 := fun c => HEq.trans (a3 c) (hm.jE c)
  have b6 := fun c => HEq.trans (a4 c) (hm.jM c)
  have b7 := fun c => HEq.trans (a5 c) (hm.jX c)
  have b8 := HEq.trans a6 hm.eW
  have b9 := HEq.trans a7 hm.jMt
  have c1 := fun j v => (he j v).trans (m.eta j ((by with_unfolding_all exact (v :))))
  have c2 := fun F0 => (hW F0).symm.trans (m.W1 ((by with_unfolding_all exact (F0 :))))
  have c3 := fun c u => HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c u).j) hA)) (m.tA c u)
  refine ⟨{ z := Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((Dat.holds_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.intersectionNumber_baseChange) :))
            exAt := (by with_unfolding_all exact ((Dat.exAt_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.exAt) :))
            inGeo := (by with_unfolding_all exact ((Dat.inGeo_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => coreP_transfer s (m.core h)
            eta := (by with_unfolding_all exact (c1 :))
            W1 := (by with_unfolding_all exact (c2 :))
            y := (by with_unfolding_all exact ((Mv.hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := (by with_unfolding_all exact (c3 :)) }, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hm.tupT :))
  · exact (by with_unfolding_all exact (b2 :))
  · exact (by with_unfolding_all exact (b3 :))
  · exact (by with_unfolding_all exact (b4 :))
  · exact (by with_unfolding_all exact (b5 :))
  · exact (by with_unfolding_all exact (b6 :))
  · exact (by with_unfolding_all exact (b7 :))
  · exact (by with_unfolding_all exact (b8 :))
  · exact (by with_unfolding_all exact (b9 :))

end Move

theorem exists_moved_loc : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))), ∃ m : Moved (oL x L), m.z = datL x L ∧ m.Copy ∧ m.Coh := by
  intro K B f T w P x L
  obtain ⟨m, h1, h2⟩ := exists_moved_transfer (o := x.o) (o' := oL x L) (sameL x L) x.m x.coh
  exact ⟨m, h1, copy_transfer (o := x.o) (o' := oL x L) (sameL x L) x.copy h1, h2⟩

end GlobalTheory.HeightCounting.Fin3.MvLoc

end
