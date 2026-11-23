import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainComparisonTransferOtherLaterStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeRepresentativesPartsOtherLaterStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.Mv

namespace GlobalTheory.HeightCounting.Up.MvTw

section Gen

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C)
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m}

section Comp
variable (R : RealDat3 a.D A3 Ks)

def once : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) := real3 c R

def thru : @RealDat3 c.D G _ _ Pl0 I0 T₀ (famInThreeCoefficientChange c A3) Ks _ _ (alg c iK) :=
  (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thruY : letI := alg c iK; type_of% (once c R).ioY := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioY :))

def thruX : letI := alg c iK; type_of% (once c R).ioX := letI := alg c iK; (by with_unfolding_all exact ((thru b c R).ioX :))

theorem thruY_eq : letI := alg c iK; (once c R).ioY = thruY b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioY c R.toRealDat).symm :)) : HEq (once c R).ioY R.ioY)
    ((by with_unfolding_all exact ((HEq.trans (real_ioY b R.toRealDat) ((by with_unfolding_all exact ((real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruY b c R)) :))))

theorem thruX_eq : letI := alg c iK; (once c R).ioX = thruX b c R :=
  letI := alg c iK
  eq_of_heq (HEq.trans ((by with_unfolding_all exact ((real_ioX c R.toRealDat).symm :)) : HEq (once c R).ioX R.ioX)
    ((by with_unfolding_all exact ((HEq.trans (real_ioX b R.toRealDat) ((by with_unfolding_all exact ((real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)) :))) :
    HEq _ (thruX b c R)) :))))

theorem thru_eq : once c R = thru b c R :=
  letI := alg c iK
  (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (once c R)) (thruY_eq b c R) (thruX_eq b c R)) :))

end Comp

variable {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat) (y' : HdB b R.toRealDat)

set_option maxHeartbeats 1000000 in

theorem pkT_move (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (GlobalTheory.Mem.R3.Tr.reps_parts_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.Mem.R3.Rw.chT_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.Mem.R3.Rw.lfT_of_same B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.Mem.R3.Rw.rr_eta_tr B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Gen

section Dat

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

set_option maxHeartbeats 1000000 in

theorem transportModuliCoreWithConstants_comp (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc b.st.B px → b.st.B.LL)) (tr : TrI b.st.B px)
    (co : Formalism.L2.Pj.CoreJ b.st.toD7) (al : Algebra co.Q.c.F b.st.toD7.what₂.LL)
    (ale : ∀ y : co.Q.c.F, b.st.B.embLL (algebraMap co.Q.c.F b.st.toD7.what₂.LL y) = y)
    (R : RealDat3 b.st.toD7 (famR b.st I hX (usedOf I T Wt) Xg tr) co.Q.c.F)
    (hXg : Xg = z₀.Xg) (htr : tr = z₀.tr)
    (hc : HEq co (coreJ (a := a) b z₀.core)) (hR : HEq R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c co) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := al) R) (real3 (a := a) c (iK := z₀.alg) z₀.R) := by
  have hc' := eq_of_heq hc
  subst hXg htr hc'
  have e : al = ((by with_unfolding_all exact ((alg (a := a) b z₀.alg) :))) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    refine Eq.trans (ale y) ?_
    exact (by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :))
  subst e
  have hR' : R = ((by with_unfolding_all exact ((real3 (a := a) b (iK := z₀.alg) z₀.R) :))) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  refine ⟨?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := a) c z₀.core)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (thru_eq (a := a) b c (iK := z₀.alg) z₀.R).symm) :))

set_option maxHeartbeats 1000000 in

theorem copy_comp (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (hXg : z.Xg = z₀.Xg) (htr : z.tr = z₀.tr)
    (hc : HEq z.core (coreJ (a := a) b z₀.core)) (hR : HEq z.R (real3 (a := a) b (iK := z₀.alg) z₀.R)) :
    HEq (coreJ (a := b) c z.core) (coreJ (a := a) c z₀.core) ∧
      HEq (real3 (a := b) c (iK := z.alg) z.R) (real3 (a := a) c (iK := z₀.alg) z₀.R) :=
  (by with_unfolding_all exact ((transportModuliCoreWithConstants_comp b c z₀ z.Xg z.tr z.core z.alg z.alg_eq z.R hXg htr hc hR) :))

end Dat

section Main

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}

set_option maxHeartbeats 2000000 in

theorem moved_again (o o' : q.Over) (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hc : m.Copy) (hh : m.Coh) :
    ∃ m' : Moved o', m'.z = DatCopy.copy (a := o.Z) o'.Z s m.z ∧ m'.Copy ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_move (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.Mem.R3.Rw.rr_eta_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hk := copy_comp (a := Z₀) o.Z o'.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :)))
  have hW := forcedContentPlaces_eq_transport_sameFiniteGroup (a := o.Z) o'.Z s m.z
  refine ⟨{ z := DatCopy.copy (a := o.Z) o'.Z s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((cp_holds (a := o.Z) o'.Z s m.z m.intersectionNumber_baseChange) :))
            exAt := DatCopy.copy_exAt (a := o.Z) o'.Z s m.exAt
            inGeo := (by with_unfolding_all exact ((cp_inGeo (a := o.Z) o'.Z s m.z m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := o.Z) o'.Z (m.core h).1) :)), (by with_unfolding_all exact ((m.core h).2.1 :)), (by with_unfolding_all exact ((m.core h).2.2.1 :)),
              (by with_unfolding_all exact ((m.core h).2.2.2 :))⟩
            eta := fun j v => Eq.trans ((by with_unfolding_all exact ((he j ((by with_unfolding_all exact (v :)))) :)) : _ = etaOf m.z.R m.z.F j v) (m.eta j v)
            W1 := fun F0 => Eq.trans ((by with_unfolding_all exact ((hW ((by with_unfolding_all exact (F0 :)))) :)) : _ = m.z.W1 ((by with_unfolding_all exact (F0 :)))) ((by with_unfolding_all exact ((m.W1 ((by with_unfolding_all exact (F0 :)))) :)))
            y := (by with_unfolding_all exact ((hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c ((by with_unfolding_all exact (u :)))).j) hA))
              (m.tA c ((by with_unfolding_all exact (u :))))) :)) }, rfl, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hk.1 :))
  · exact (by with_unfolding_all exact (hk.2 :))
  · exact (by with_unfolding_all exact (hh.tupT :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PY :)) : HEq (fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PY.ψ m.y.PY.ψ) hh.PY) :))
  · exact (by with_unfolding_all exact ((HEq.trans ((by with_unfolding_all exact (hy.PW :)) : HEq (fun i => ((fixTup (a := o.Z) o'.Z (iK := m.z.alg) m.y y').PW i).ψ) (fun i => (m.y.PW i).ψ)) hh.PW) :))
  · exact (by with_unfolding_all exact ((a2.trans hh.rep) :))
  · exact (by with_unfolding_all exact ((fun c => (a3 c).trans (hh.jE c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a4 c).trans (hh.jM c)) :))
  · exact (by with_unfolding_all exact ((fun c => (a5 c).trans (hh.jX c)) :))
  · exact (by with_unfolding_all exact ((a6.trans hh.eW) :))
  · exact (by with_unfolding_all exact ((a7.trans hh.jMt) :))

end Main

theorem moved_tw {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (N : TwNew (Dof x)) : ∃ m : Moved (oTw x N), m.z = datTw x N ∧ m.Copy ∧ m.Coh :=
  moved_again x.o (oTw x N) (sgTw x N) x.m x.copy x.coh

end GlobalTheory.HeightCounting.Up.MvTw

end
