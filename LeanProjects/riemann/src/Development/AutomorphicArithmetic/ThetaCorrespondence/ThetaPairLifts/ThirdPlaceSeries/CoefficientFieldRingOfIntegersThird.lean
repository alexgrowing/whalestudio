import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyTiedAllStatesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdComponentFitsIntegralLattice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsParamsAtMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdComponentHeckeCharacterTuple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTypesWithLocalConditions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDivisorEigenIndexThirdComponent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThirdComponentsAgree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrdinaryIdempotentThirdComponentOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PinOfNTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
set_option maxHeartbeats 4000000 in
theorem third_place_fixed_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : _root_.GlobalTheory.NPin.CharacterChoiceData hL (withLoc L), Q.cf = cfL L (cfOf x) ∧ Q.C = chL L l.c.ch ∧ HEq Q.tp (tpL L l.c.tp) ∧
      HEq Q.rep (repOf x.r.Y) ∧ HEq Q.M (mtL L l.mt.M) := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
      eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) :=
    ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.NPin.exists_character_choice_of_nTrue_split hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, h1, h2, h3, h4, h5⟩
end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
open GlobalTheory.HeightCounting.Fin3 GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 4000000 in
theorem readCoefField_eq_cfL_of_moved_copy_coherent : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → m.z.R.C = cfL L (cfOf x) := by
  intro hL _ _
  exact StepW.of_all fun K B f T w _ _ _ P x l big L hB hO m _ _ s r _ => m.z.lev.C
set_option maxHeartbeats 4000000 in
theorem third_place_linked_data_exists : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedData hL D') := by
  intro hL hP hX
  have H := ((_root_.GlobalTheory.HeightCounting.Up.ThirdFits.third_component_fits_integral_lattice_alt hL hP hX).and (GlobalTheory.HeightCounting.Up.GapAllStates.gapR_allSt)).and (_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt.2.and ((_root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.readCoefField_eq_cfL_of_moved_copy_coherent hL hP hX).and
    ((_root_.GlobalTheory.HeightCounting.Up.ThirdTied.third_component_hecke_character_tuple_alt hL hP hX).and ((_root_.GlobalTheory.HeightCounting.Fin.finite_types_with_local_conditions_alt hL hP hX).and ((_root_.GlobalTheory.T.eigen_index_divisibility_of_cmDatum_alt hL hP hX).and
    ((_root_.GlobalTheory.HeightCounting.Up.ThirdAgree.third_components_agree_alt hL hP hX).and (_root_.GlobalTheory.T.ordinary_idempotent_third_component_of_cmDatum_alt hL hP hX)))))))
  refine H.trans (StepW.of_all fun K B f T w _ _ h P x l => ?_)
  obtain ⟨⟨hfits, hgap⟩, hpar, hcf, htp, hty, hidx, hag, he0⟩ := h
  refine ⟨fun _ => ∅, fun L hB hO => ?_⟩
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_fixed_alt hL hP x l _ L hB
  obtain ⟨x', hx'⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState hX.weil hX.ds hP.hc hP.decay K B f T w P (oL x L) (hfits P x l _ L hB hO) x.G_eq
    x.etaF (bkL L)
  obtain ⟨o, fits', G_eq', etaF', bk', m, cp, co, s, r, pn⟩ := x'
  dsimp only at hx'
  subst hx'
  have hC := hcf P x l _ L hB hO m cp co s r pn
  have ht := htp P x l _ L hB hO m cp co s r pn
  have hT := hty P x l _ L hB hO m cp co s r pn
  obtain ⟨Xd, E, ⟨labPi⟩⟩ := hidx P x l _ L hB hO m cp co s r pn
  have hg : GlobalTheory.LiftRows.Given m.z.R.toRealDat m.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak m.z.R m.z.F m.z.pins.char m.exAt).1, (hpar P x).2 L, m.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ m.z.pins.char.base.lev hT, m.z.pins.keep.guard, hgap P x⟩
  obtain ⟨ag⟩ := hag P x l _ L hB hO m cp co s r pn hC Xd E labPi m.z.pins.char.base ht hg m.z.pins.char.fullP Q.rep h4
  have e0 := he0 P x l _ L hB hO m cp co s r pn hC Xd E labPi m.z.pins.char.base ht hg m.z.pins.char.fullP
  obtain ⟨T0, -, -⟩ := _root_.GlobalTheory.HeightCounting.Up.RealOfReading.exists_linked_data_of_agreement Q (realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi
    m.z.pins.char.base ht hg m.z.pins.char.fullP) h1 h2 h3 (eq_of_heq h5) HEq.rfl ag e0
  exact ⟨T0⟩
end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_system_third_place_linked_data : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedData hL D') := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_linked_data_exists | exact _root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_linked_data_exists | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_linked_data_exists <;> assumption)
end
end
