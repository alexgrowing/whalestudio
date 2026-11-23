import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.JoinModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop}
variable {G : Type} [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw}
  {YS : NExpRealS R cG S} {cf : CharFrame D}
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
variable {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
def twistInputsOfBaseTuples {hH hV hs} (Y : SerSide (realOf t hH hV hs) (twEOf xd))
    (hS : Y.S = ratDatR t.r.z.R t.r.z.cG c.row.kKs c.row.hk) (hY : HEq Y.YS c.row.nexp) (g : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7)
    (h1 : g.cf = TC.cf w.I w.l Z) (h2 : g.lam.C = TC.cf w.I w.l Z) (hF : FieldOk (realOf t hH hV hs))
    (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (w.st Z).toD7 g.wd)
    (hb : T = TwDat.untw B T.pl → ∀ v, (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 → BaseTup Y (nch.twI v)) :
    _root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c :=
  ⟨realOf t hH hV hs, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, Y, hS, hY, g,
    h1, h2, t.r.z.lev.C, hF, cg, hb⟩
def heckeSeriesOfRealHeight {hH hV hs} (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)
    (H : NExpRealH t.r.z.R t.r.z.cG _ c.row.nexp) (hr : GlobalTheory.ExportPin.Reads t.r.z.R t.r.z.cG _ c.row.nexp H.hL)
    (hd : ∀ i b P, P ∉ (w.D Z).ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G (w.D Z).host.E (w.D Z).nd.Om,
      Formalism.ConjugateSelfDual.IsFrob (F := (w.D Z).host.E) ((w.D Z).nd.plOm.1 P) (Formalism.ConjugateSelfDual.normV P) σ →
      H.cHk i b 1 P = algebraMap ((w.D Z).ntw.O i) (FractionRing ((w.D Z).ntw.O i)) (algebraMap ((w.D Z).ntw.O0 i) ((w.D Z).ntw.O i)
        ((if b then (w.D Z).ntw.delta i σ else ((w.D Z).ntw.delta i σ)⁻¹ : ((w.D Z).ntw.O0 i)ˣ) : (w.D Z).ntw.O0 i)))
    (hk_emb : ∀ i j b k P (x : (w.D Z).ntw.B i j b), 1 ≤ j → j ≤ B.R.m → IntegralHeckeForms.HkIdx i k P →
      (w.D Z).nexp.embB i j b ((w.D Z).ntw.hk i j b k P x) = (w.D Z).nexp.hkF i j b k P ((w.D Z).nexp.embB i j b x))
    (hz : ∀ i (s : (w.D Z).ntw.Sig i) P, (w.D Z).ntw.hEig i s 0 P = 1) : SerSide (realOf t hH hV hs) (twEOf xd) where
  S := _
  YS := c.row.nexp
  sup := e.ser.sup
  H := H
  reads := hr
  del := hd
  Z := e.ser.ex
  U_eq g := (c.row.grp.lvl0 g).symm
  psi_eq := psi_of_grp c.row.grp e.ser.ex
  low := low_of_tied c.a.all.tw (q_dvd_discr _)
  Sb i P hP := by
    have hA : t.r.z.R.Sb = t.r.z.R.Pg := t.r.z.pins.char.allPl
    obtain ⟨k, hk⟩ := e.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true P
      (by rw [e.ser.ex.pin.Pg]; exact hA ▸ hP)
    exact (w.D Z).ntw.placesOver_subset_exceptional i k hk
  B_range i _ j _ b := c.a.all.tw.B_range i j b
  hk_emb := hk_emb
  hk_split i _ j _ b k P h := by
    obtain ⟨s, hs⟩ := c.a.all.tw.hk_split i j b k P h.2.2.2
    exact hs ▸ Polynomial.Splits.multisetProd fun p hp => by
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp
      exact Polynomial.Splits.X_sub_C a
  off i _ := ⟨fun j hj b => e.ser.off i j b fun h => hj (Finset.mem_Icc.2 h), hz i⟩
  all i j hj b a := by
    have := e.xd i j b (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
    change a ∈ xd.xd0 i j b
    rw [this]; trivial
theorem exists_wdTie_cgTrue_labTrue_of_built {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) :
    ∃ wd : GlobalTheory.RowTie.WDTie D.nd D.naut, Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D wd) ∧ LabTrue D wd := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨{ A.wdT with }, ⟨{ cg with }⟩, A.lab⟩
theorem exists_galSide_of_rank_ge_hundred (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) (h3 : _root_.GlobalTheory.Triple.IsGaloisTriple (w.D Z)) (hr : 100 ≤ B.R.r)
    (hg : ∀ k, 2 * B.R.r ≤ B.host.g k) : ∃ g : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, g.cf = TC.cf w.I w.l Z ∧ g.lam.C = TC.cf w.I w.l Z ∧
      Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL (w.st Z).toD7 g.wd) := by
  obtain ⟨wd, cg, lab⟩ := _root_.GlobalTheory.TwInputs.JoinModel.exists_wdTie_cgTrue_labTrue_of_built c.a.nt.toNBuilt
  exact ⟨⟨wd, lab, TC.cf w.I w.l Z, { c.a.chrN with }, h3, e.ser.lam, e.ser.lam_ok, fun i hi => (e.ser.lam_tie i hi).imp id (Exists.imp fun _ h => ⟨h.1, h.2.1⟩), hr, hg⟩, rfl, e.ser.lam_C, cg⟩
theorem embB_hk_commute_and_hEig_zero_of_built {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) :
    (∀ i j s k P (x : D.ntw.B i j s), 1 ≤ j → j ≤ D.R.m → IntegralHeckeForms.HkIdx i k P →
      D.nexp.embB i j s (D.ntw.hk i j s k P x) = D.nexp.hkF i j s k P (D.nexp.embB i j s x)) ∧
    ∀ i (s : D.ntw.Sig i) P, D.ntw.hEig i s 0 P = 1 := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  exact ⟨fun i j s k P x h1 h2 h => Bs.hk_emb i j s k P x h1 h2 h.2.2.2 h.2.2.1 h.2.1, Bs.hEig_zero⟩
end Rows
end GlobalTheory.TwInputs.JoinModel
end
end
