import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftsOfRationalFormsRationalOfClausesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTestBOfRatG
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MLat3OfTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalIffRecord
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem liftTests_and_mLat_of_ties : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) ∧ Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false ∧ (R.toCx3 F).MLat false := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hB hG
  obtain ⟨hCore, hOff, hUsed⟩ :=
    GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 _ R F hB.char hB.ex
  obtain ⟨fw, -⟩ := hG.fw
  have hM : R.toRealDat.IsModels := hB.char.base.models
  have hEv : EvInj T R.toRealDat v₀ := GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie T R.toRealDat κ v₀ hM fw
  have hRat : GlobalTheory.TwistField.RatG R.toRealDat (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) :=
    GlobalTheory.T.thetaLifts_of_rationalForms_rational_of_clauses D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O _ hB.nV hCore hOff hUsed ⟨fw⟩ hG.pins
      (fun i => hG.phase i hG.unif) hG.ioExt (fun i => (hG.oneMap i).1) hB.guard hG.unif hEv hG.cover
  have hLB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false :=
    GlobalTheory.TwistField.liftTestB_of_ratG D G Pl0 I0 T0 A3 _ R F false hG.unif hRat
  exact ⟨GlobalTheory.LiftTestCompare.liftTest_of_liftTestB _ hLB, hLB,
    GlobalTheory.GoodLat.Obj3.mLat3_of_tie T R F κ v₀ fw⟩

end GlobalTheory.PrimIn

end
