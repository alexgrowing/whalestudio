import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkPlacesStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamSplit
end GlobalTheory.FamSplit
namespace GlobalTheory.FamSplit
theorem split_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ), j < D.R.m → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ), IsSDFrame V β Λ 1 ∨ IsSDFrame V β Λ (D.host.g 0 * D.host.g 1) → IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ vac → ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W j M Λ β vac dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t j M Λ β vac dQ ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac v ↔ v = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG vac) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW j hj V S M Λ β vac hSD hvac
  have hLev := hW.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hY⟩ := hLev.βY j hj
  have sdY : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j hj)
  have frY : Formalism.L2.DIV.IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) := hY.1
  have sdV : IsSelfDualC V Λ := hSD.elim (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _)
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _)
  have frV : Formalism.L2.DIV.IsFrame β Λ := hSD.elim (fun h => h.elim fun _ h => h.1) (fun h => h.elim fun _ h => h.1)
  have hex := GlobalTheory.PlaceDatum.stepVecExists D
  obtain ⟨⟨eG, heG⟩, hQt⟩ := _root_.GlobalTheory.T.level_places_disjoint_idempotents_alt W hW
  obtain ⟨fG, hfG⟩ := hex (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
    (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ∅
    (fun _ => 1) sdY sdV frY frV (Finset.disjoint_empty_right _) ⟨eG, heG⟩ vac hvac
  obtain ⟨dG, hdG, rfl⟩ := GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdV frY frV hfG
  have hdG' : GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) dG := by
    simpa only [datY, Finset.union_empty] using hdG
  refine ⟨dG, ⟨hdG', hfG⟩, fun t => ?_⟩
  obtain ⟨hdis, hne, ⟨e, he⟩, ⟨eQ, heQ⟩⟩ := hQt t
  obtain ⟨fQ, hfQ⟩ := hex (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β
    (datY _ D.R.r D.R.t j (r_le_Y j) ∅ ((_root_.GlobalTheory.Fam.pk_z W).Q t) (LevelP.triv _ _ _) (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) Frm.B)
    ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) sdY sdV frY frV (Finset.disjoint_empty_left _) ⟨eQ, heQ⟩ vac hvac
  obtain ⟨dQ, hdQ, rfl⟩ := GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdV frY frV hfQ
  have hdQ' : GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 D.host.F)) dQ := by
    simpa only [datY, Finset.empty_union] using hdQ
  have hfull := GlobalTheory.T.thetaStepVector_eq_tupleComb_of_levelComb D _ _ (Yc D j) V _ _ _ _ _ _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi
    ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac dG dQ sdY sdV frY frV hdis hne ⟨e, he⟩ hdG' hdQ' hfG hfQ
  refine ⟨dQ, ⟨hdQ', hfQ⟩, fun v => ⟨fun hv => stepVecOf_unique hv hfull, ?_⟩⟩
  rintro rfl
  exact hfull
end GlobalTheory.FamSplit
end
