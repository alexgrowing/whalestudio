import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteTypeEqISupSplitTrivialTranslatesLocal
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteType_eq_iSup_splitTrivial_translates_local : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, ∃ b, NG.rt L n x (T a) = T b) → π.S = ⨆ y : {y : GAf L n // TrivOutside {s.v}ᶜ y}, LinearMap.range ((NG.rt L n y.1).comp T) := by
  first | exact @GlobalTheory.SerSys.finTyp_eq_iSup_rt_local | exact GlobalTheory.SerSys.finTyp_eq_iSup_rt_local | (intros; apply GlobalTheory.SerSys.finTyp_eq_iSup_rt_local <;> assumption)
