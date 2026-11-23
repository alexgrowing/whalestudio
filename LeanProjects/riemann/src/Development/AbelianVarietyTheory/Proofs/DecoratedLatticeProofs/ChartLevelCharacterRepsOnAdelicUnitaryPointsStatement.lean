import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevelCharacterReps_on_adelicUnitaryPoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} (K : LevelChart (I.rec7 l Z) T bad i hi stab lat), ∃ (U : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))) (chi : U →* ℂˣ) (h : cl → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)), (∀ g, g ∈ U ↔ g ∈ GfC _ ∧ ∃ κ : K.lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧ (∀ (g : U) (κ : K.lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi g = K.lev.chi κ) ∧ (∀ c, h c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h c) = (K.y c).1.1) := by
  first | exact @GlobalTheory.ChartLevRead.levData | exact GlobalTheory.ChartLevRead.levData | (intros; apply GlobalTheory.ChartLevRead.levData <;> assumption)
