import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.Divisors.Params
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimRows3OfParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialLFunctionFromPrintResultsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneGivesLiftDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneGivesUnitEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneRationalRowsSizedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestPositiveLevelsKappaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealDataWeightVectorFamilyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Closing3

theorem primRows3_typesSep3 : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → PrimRows3 R F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  intro P hRSW hHL eps heps
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.multiplicity_one_rational_rows_sized P eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O L hLe hLx hSz hPar hT hG hM hRT
  obtain ⟨_hGiven, hGS, hCD, hLI, _hTR, _hUI, _hUIW⟩ := GlobalTheory.T.multiplicity_one_gives_lift_data P R F hT hM
  obtain ⟨hOk, hGU, hGE, _hBlk, hA, hB⟩ := GlobalTheory.T.multiplicity_one_gives_unit_equiv P R F hT hM
  obtain ⟨hPos, hK, hH2⟩ := hx₀ R F L hLe hLx hSz hPar hT hM hRT
  obtain ⟨hLT, hLTB, hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  have hU : R.toRealDat.LUnif := hG.unif
  obtain ⟨_hLev, _hW, hHk, hTS, htr⟩ := GlobalTheory.T.lift_test_positive_levels_kappa P R F hT hM hU hLT hPos hK
  obtain ⟨hGal, hPP⟩ := GlobalTheory.T.real_data_weight_vector_family P hRSW hHL T R F κ v₀ O hT hG hM hRT hPos hK
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hOnto := GlobalTheory.T.partial_L_function_of_hypotheses P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hRSW hHL R F hT.ok hT.char hT.ex hT.host hT.params
    hT.ccK hT.guard hT.types hOk.2 hGE hU
  have hPrim := GlobalTheory.primRows3_of_parts P.q2 P.q1 R F hLI hT.ok hT.char hT.ex hJ hGS hCD hM hOk.1 hOk.2 hHk hGU hGE hRT hLT hLTB
    hOnto hPos hPP hH2 hB hU hML hA hGal
  exact ⟨hPrim, hTS, htr⟩

end GlobalTheory.Closing3
