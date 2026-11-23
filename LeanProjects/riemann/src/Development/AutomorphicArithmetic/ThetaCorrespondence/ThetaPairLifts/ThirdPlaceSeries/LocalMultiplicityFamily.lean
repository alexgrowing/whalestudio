import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
variable (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
def yStructureLocal : NExpRealS (datL x L).R (datL x L).cG (SL L l.rat) where
  fi := (by with_unfolding_all exact (l.b.YS.fi :))
  geq := (by with_unfolding_all exact (l.b.YS.geq :))
  rho := (by with_unfolding_all exact (l.b.YS.rho :))
  chi := (by with_unfolding_all exact (l.b.YS.chi :))
  eF := kc% l.b.YS.eF
  bsup := kc% l.b.YS.bsup
  act := kc% l.b.YS.act
def heckeHeightData : NExpRealH x.m.z.R x.m.z.cG l.rat.S l.b.YS where
  hL := l.rat.In.hL
  hs := l.b.Bs.hs
  cHk := fun i b k Q => algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) (l.b.Bs.cHk i b Q) ^ k
  cHk_zero := fun i b Q => pow_zero _
  cHk_unit := fun i b Q =>
    ((l.b.Bs.cHk i b Q).isUnit.map (algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)))).pow 1
  cHk_pow := fun i b k Q => by simp only [pow_one]
  hkEq := by rw [l.b.eF]; exact l.b.Bs.hkEq
def localHeckeHeightData : NExpRealH (datL x L).R (datL x L).cG (SL L l.rat) (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) where
  hL := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).hL :))
  hs := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).hs :))
  cHk := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).cHk :))
  cHk_zero := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).cHk_zero :))
  cHk_unit := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).cHk_unit :))
  cHk_pow := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).cHk_pow :))
  hkEq := kc% (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).hkEq
def psiVectorLocal : ∀ i : Fin (DL x L).R.m, principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (DL x L) i) (DL x L).R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oL x L).Z (l.mt.ad.PV ((i)))) : _))
def characterChoiceLocal : NChoice (DL x L) := (by with_unfolding_all exact ((chL L l.c.ch) :))
def localCharacterTupleAgreement : TupTied (DL x L) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) := (by with_unfolding_all exact ((tpL L l.c.tp) :))
def localMultiplicityFamily : MtFam (DL x L) := (by with_unfolding_all exact ((mtL L l.mt.M) :))
def placeMapLocal : HeightOneSpectrum (𝓞 (maximalRealSubfield (DL x L).host.E)) → PlE (DL x L).host := (by with_unfolding_all exact (l.Pq :))
def localEigenvalueDegree : ℕ → (DL x L).what₂.FT → ℕ → PlE (DL x L).host → ↥(DL x L).LL0 := (by with_unfolding_all exact (l.rat.In.eig :))
def smallPlaceSet : Finset (PlE (DL x L).host) := (by with_unfolding_all exact (l.rat.In.Sb :))
theorem twist_ok_local : ∀ v, TwistedAt (DL x L) v → IntegralHeckeForms.TwOK ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).k' v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v)
    (((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).psi' v).comp ((DL x L).ntw.art ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).twI v) ((_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l).Q v))) := (by with_unfolding_all exact (l.c.ok :))
theorem thetaTie_yStructureLocal_nonempty : Nonempty (GlobalTheory.GeoTie.ThetaTie (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.fw (DL x L).nth) := by
  obtain ⟨g⟩ := l.b.geo
  exact ⟨⟨fun i j b => ⟨(by with_unfolding_all exact ((g.side ((i)) ((j)) b).pt : _)), (by with_unfolding_all exact ((g.side ((i)) ((j)) b).cover : _)),
    (by with_unfolding_all exact ((g.side ((i)) ((j)) b).ev_eq : _)), kc% (g.side (kc% i) (kc% j) b).fmUr, (by with_unfolding_all exact ((g.side ((i)) ((j)) b).hk : _)),
    (by with_unfolding_all exact ((g.side ((i)) ((j)) b).hk_none : _))⟩, (by with_unfolding_all exact (g.isUnramified₂ :))⟩⟩
theorem kept_characterChoiceLocal : Kept l.c.ch (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) :=
  ⟨sameGaloisL L, twistDataAgreeAcrossCoefficients_localized L, sameFormsL L, (by with_unfolding_all exact ((HEq.refl (Dof x).ntwbr) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.twI) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.sd) :)),
    (by with_unfolding_all exact ((HEq.refl l.c.ch.Q) :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.k') :)), (by with_unfolding_all exact ((HEq.refl l.c.ch.psi') :))⟩
theorem yStructureLocal_fi_e_heq : ∀ i y, HEq (((_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l).fi i).e y) y := (by with_unfolding_all exact (l.b.fi :))
end GlobalTheory.HeightCounting.Fin3
end
end
