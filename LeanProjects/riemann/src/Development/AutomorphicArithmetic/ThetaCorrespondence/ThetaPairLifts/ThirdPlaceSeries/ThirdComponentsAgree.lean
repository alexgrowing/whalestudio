import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AgreeOfData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ThirdAgree
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
section Copy
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}
end Copy
section Main
set_option maxHeartbeats 4000000 in
theorem third_components_agree_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf (rep : (withLoc L).what₂.FT → NG.FinTyp (withLoc L).host.E (withLoc L).R.r), HEq rep (repOf x.r.Y) → Nonempty (GlobalTheory.NJoin.Agree (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) (mtL L l.mt.M) rep) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m hcp hco s r hpin hC Xd E labPi hb htup hg hf rep hrep
  have c1 := cV_copy (B := B) (C := w.C) (a := P.Z₀) (GlobalTheory.HeightCounting.Fin3.oL x L).Z P.z m.z m.Xg m.tr ((by with_unfolding_all exact (hcp.core :))) ((by with_unfolding_all exact (hcp.R :)))
  have c0 := cV_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :)))
  have ecV := cV_two (a := P.Z₀) x.o.Z (GlobalTheory.HeightCounting.Fin3.oL x L).Z c0 c1
  have hJ : HEq m.t.lf.jMt x.m.t.lf.jMt := hco.jMt.trans x.coh.jMt.symm
  have kJ : ∀ μ (i : Fin (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7.R.m) y,
      HEq (m.t.lf.jMt μ i y) (x.m.t.lf.jMt ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) := fun μ i y => (by with_unfolding_all exact ((heq_apply (D := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7) (Mt := fun μ j => (P.q.p.sL μ j).A) ecV
      ((m.t.lf.jMt)) ((x.m.t.lf.jMt)) ((hJ)) μ i y) : _))
  have eR1 : m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq hco.rep) :))
  have eR0 : x.m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq x.coh.rep) :))
  have eRep : rep = (by with_unfolding_all exact ((repOf x.r.Y) :)) := (by with_unfolding_all exact ((eq_of_heq hrep) :))
  have hrep' : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)) := by
    intro σ
    have a1 : (rep σ).Iso ((by with_unfolding_all exact ((repOf x.r.Y σ) :))) := (by with_unfolding_all exact ((iso_of_eq (congrFun eRep σ)) :))
    have a2 := x.pin.rep ((by with_unfolding_all exact (σ :)))
    have a3 : ((by with_unfolding_all exact ((x.m.t.rep σ) :)) : NG.FinTyp (withLoc L).host.E (withLoc L).R.r).Iso ((by with_unfolding_all exact ((m.t.rep σ) :))) := (by with_unfolding_all exact ((iso_of_eq ((congrFun eR0 σ).trans (congrFun eR1 σ).symm)) :))
    have a4 := NG.IsoRep.symm (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)).stable (hpin.rep σ)
    exact (by with_unfolding_all exact ((NG.IsoRep.trans a1 (NG.IsoRep.trans a2 (NG.IsoRep.trans a3 a4))) :))
  let DL := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7
  let jm : ∀ μ, Used0 DL μ → ∀ i : Fin DL.R.m, DL.what₂.Mt μ (i.1 + 1) → GA DL (Vc DL i) →
      (cpV (GlobalTheory.HeightCounting.Fin3.oL x L).Z x.m.z.R.cV i).W :=
    fun μ h i y => (by with_unfolding_all exact ((x.r.Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))
  have hj : ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (jm μ h i y) := fun μ h i y => (by with_unfolding_all exact (((hpin.jMt μ h i y).trans ((kJ μ i y).trans (x.pin.jMt μ h i y).symm)) :))
  exact (by with_unfolding_all exact ((agree_of_data (D := DL) (R := m.z.R) (F := m.z.F) r.Y (cf := ((cfL L (cfOf x)))) (nch := ((chL L l.c.ch)))
    (((tpL L l.c.tp))) ((hC)) ((Xd)) ((E)) ((labPi)) ((hb)) ((htup)) ((hg)) ((hf)) (((mtL L l.mt.M))) ((rep))
    ((hrep')) _ ecV (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) ((l.mt.ad.std)) ((l.mt.ad.eW)) jm hj ((l.mt.ad.read)) ((l.mt.ad.rat))
    ((l.mt.ad.wt))) : _))
end Main
end GlobalTheory.HeightCounting.Up.ThirdAgree
end
end
end
