import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowPartNeBotPositiveDimension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesLiftData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesUnitEquiv
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PartialLFunctionOfPublished
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn GlobalTheory.LiftRows
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.LiftsOnly
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
section Real
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Real
set_option maxHeartbeats 1000000 in
theorem holdsL_of_ties_alt (P : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) (hHL : GlobalTheory.Published.HeckeLPartialContinuation)
    (eps : ℝ) (heps : 0 < eps) : ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
      {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
      (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
      (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
      (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x →
      Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat →
      R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Rw.HoldsL R F := by
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.LiftRows.goodForms_definite_exist (GlobalTheory.DefFree.goodVectorsDefinite P.q12) eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O L hLe hLx hSz ⟨pV⟩ hT hG hM hInt
  obtain ⟨hGiven, hGS, hCD, -, hTR, hUp, -⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  obtain ⟨hOk, hGU, hGE, hBlk, hA, hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  obtain ⟨hLT, hLTB, hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  have hU : R.toRealDat.LUnif := hG.unif
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay P.q2 R.toRealDat
  have hRows : RowsNe R.toRealDat F.lv2 := GlobalTheory.RowsNeProof.rowsNe R.toRealDat F.lv2 1 hT.ok.ok2 hcore.1 hSch R.SF hcore.2.1 hTR
    (hx₀ D L pV hLe hLx hSz R.toRealDat F.lv2 hGiven)
  have hCar := carries_of_upInj P.q2 P.q1 R F hT.ok hT.char hT.ex hT.junk hGE hUp
  obtain ⟨hScal, hMatch, -, -⟩ := GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8
    (_root_.ResidueKilled.sec_of_dm P.q9) P.q10 P.q11 R.toRealDat F.lv2 hGiven hT.ccK hT.char.allPl
    (GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex) R.SF hcore.2.1 hTR
  have hK := GlobalTheory.PosAtBase.pos_at_base R F hT.ok hT.char hT.ex hScal hMatch
    (GlobalTheory.CarriesOne.parts_eq_of_carries P.q1 P.q2 R F hT.ok hT.char hT.ex hJ hUp)
    (exists_rowPart_ne_bot_positiveDimension P.q2 R F hT.char hT.ex hCar hRows)
  have hLev := levW_of_span P.q2 R F hT.ok hT.char hT.ex hGS hCD hM hBlk hCar hK hA hLT hU
  have hW := partsW_of_carried P.q2 R F hT.ok hT.char hT.ex hGS hCD hM hOk.1 hCar hK hB hU
  obtain ⟨-, hH, hTS, -⟩ := GlobalTheory.Hk3.HeckeClose.heckeClose P.q1 P.q3 P.q2 R F 1 hT.ok hT.char hT.ex hT.junk hT.ser hT.trSem hU
    hGU hGE hLev hA hB hK hW
  have hOnto := _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hHL R F hT.ok hT.char hT.ex hT.host hT.params
    hT.ccK hT.guard hT.types hOk.2 hGE hU
  obtain ⟨fw, hbar⟩ := hG.fw
  have hConj : R.toRealDat.PConj := GlobalTheory.ConjNorm.pConj T R.toRealDat F.lv2 κ v₀ hcore.1 hSch fw hbar hU
  have hLW : R.toRealDat.LLevelW F.lv2 :=
    GlobalTheory.LevelForms.levelW_of_irr _ _ hT.ok.ok2.irr hU hT.char.base.models.HW
  exact ⟨hOk.1, hOk.2, hH, hGU, hGE, hBlk, hLT, hLTB, hOnto, hU, hML, hLev, hA, hW, ⟨hT.ex, hConj, hLW, hInt⟩, hT.ok, hTS⟩
end GlobalTheory.LiftsOnly
end
end
