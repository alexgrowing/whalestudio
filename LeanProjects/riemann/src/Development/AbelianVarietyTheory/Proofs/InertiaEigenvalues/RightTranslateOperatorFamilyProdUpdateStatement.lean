import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorFamilyProdUpdate
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslateOperator_familyProd_update : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i, TransLaws R i → ∀ (F : ∀ v, Eu.LX R i v), {w | F w ≠ Eu.lx0 R i w}.Finite → ∀ v, F v = Eu.lx0 R i v → Eu.famProd R i F ∈ GfC (Wc D i) ∧ ∀ x : Eu.LX R i v, Eu.Bop R i (Eu.famProd R i (Function.update F v x)) = Eu.Bop R i (Eu.famProd R i F * Eu.rep x) := by
  first | exact @GlobalTheory.RawLift.Eu.bop_famProd_update | exact GlobalTheory.RawLift.Eu.bop_famProd_update | (intros; apply GlobalTheory.RawLift.Eu.bop_famProd_update <;> assumption)
