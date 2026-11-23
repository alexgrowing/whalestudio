import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBasesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsParametersFreeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicitParametersStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem gyLay_kerT_entC : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)), V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp → ∃ (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy), GyLay K (w.D Z) t.Gt t.cmp Gy ∧ ∃ kt : KerT t.toColT Y Gy ker, ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs Y (w.tw Z)), kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h := by
  have hcl : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧ ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L := GlobalTheory.T.columnChoice_cloudBound_le_cG
  refine (StepW.and hcl (StepW.of_all (q := fun K B f T w => (∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
      ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L) → _) ?_)).trans
    (StepW.of_all fun _ _ _ _ _ _ _ h => h.2 h.1)
  intro K B f T w hO hF hP hC Z t Wt nch n Y hMu hQp
  obtain ⟨cp⟩ := hP
  obtain ⟨O, hstd, hunf⟩ := TC.lift_objects w.I w.ok w.pins w.l Z Y.Qp
  let Pl : Examples₂.EntPl (w.D Z) := Classical.choice (Formalism.BasicNotions.Examples₂.entPl_nonempty _)
  obtain ⟨Bs, hB, hok⟩ := GlobalTheory.T.trueColumnChoices_kernelDatum_adaptedBases w.I w.ok w.pins w.l Z w.l0 Y O Pl hQp hstd hunf cp.jets
  obtain ⟨vOf, Fl, htm, hw, hled⟩ := GlobalTheory.T.latticeLayer_trueColumns_intrinsic w hO hF ⟨cp⟩ Z t Wt nch n Y hMu hQp (hC Z)
  choose Lv KD hK using GlobalTheory.T.levels_kernelData_at_served_place w hO hF ⟨cp⟩ Z t Wt nch n Y hMu hQp O hstd hunf _ hok Fl htm hw
  let Y0 : G.LatInst (w.D Z) := ⟨vOf, Fl, Lv, fun _ _ _ => ⟨fun _ => 0⟩, fun _ _ _ => ⊥⟩
  exact ⟨Formalism.L2.G.Cmp.withFirst t.cmp (w.tw Z) Y0 fun u v hg =>
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (KD u v hg).up.maps,
    Formalism.L2.G.Cmp.kerAll t.Gt t.cmp (w.tw Z) Y0 KD, ⟨Formalism.L2.G.Cmp.withFirst_vram _ _ _ _, hw,
      fun L a b c X d e g h => hled Lv _ _ L a b c X d e g h⟩, ⟨O, hstd, hunf, _, hok, fun u v hg => (hK u v hg).1,
      fun u v hg => (hK u v hg).2.1, fun u v hg => (hK u v hg).2.2.1, fun u v hg => (hK u v hg).2.2.2⟩, Pl, Bs, hB, rfl⟩

end GlobalTheory.Mem.Top.Bl
