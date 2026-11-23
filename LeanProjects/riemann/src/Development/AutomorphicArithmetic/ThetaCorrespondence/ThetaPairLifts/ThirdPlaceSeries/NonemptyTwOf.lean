import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParams
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkOfBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TwInputs.AtLayer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section General
variable {D : D7}
theorem exists_frob_unit_and_hkF_zero_eq_of_built {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) (h0 : ∀ j P, b.hL j 0 P = 1) :
    (∃ u, IsFrobUnit D u) ∧
      ∀ i j s P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j s 0 P x = x := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  have h := hkF_zero_of_sideB (D := D0) Bs h0
  exact ⟨⟨Bs.cHk, Bs.cHk_del⟩, fun i j s P x => h i j s P x⟩
end General
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t n}
theorem nonempty_twOf_of_hecke_stable_reads {hH hV hs} (e : _root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c) (hF : FieldOk (realOf t hH hV hs))
    (hG : ∃ G : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, G.cf = TC.cf w.I w.l Z ∧ G.lam.C = TC.cf w.I w.l Z ∧ Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ G.wd))
    (hR : ∀ (D : D7) (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S),
      ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧
        (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL) :
    Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c) := by
  obtain ⟨g, h1, h2, ⟨cg⟩⟩ := hG
  obtain ⟨k1, k2⟩ := _root_.GlobalTheory.TwInputs.JoinModel.embB_hk_commute_and_hEig_zero_of_built c.a.nt.toNBuilt
  obtain ⟨⟨u, hu⟩, hz⟩ := _root_.GlobalTheory.TwInputs.AtLayer.exists_frob_unit_and_hkF_zero_eq_of_built c.a.nt.toNBuilt (c.a.ratIn_hL ▸ c.a.ratIn.hL_zero)
  obtain ⟨f', s1, s2, s3⟩ := hR _ (realOf t hH hV hs) _ c.row.nexp
  obtain ⟨H, r1, r2⟩ := exists_hecke (realOf t hH hV hs) _ c.row.nexp e.ser.ex f' s1 s2 s3 u hu hz
  exact ⟨_root_.GlobalTheory.TwInputs.JoinModel.twistInputsOfBaseTuples (_root_.GlobalTheory.TwInputs.JoinModel.heckeSeriesOfRealHeight e H r1 r2 k1 k2) rfl HEq.rfl g h1 h2 hF cg fun hT v hv => base_of_untw _ hT v hv⟩
end Rows
end GlobalTheory.TwInputs.AtLayer
namespace GlobalTheory.TwInputs.AtLayer
end GlobalTheory.TwInputs.AtLayer
end
end
