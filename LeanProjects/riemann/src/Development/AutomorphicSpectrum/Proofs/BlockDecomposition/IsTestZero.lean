import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open Classical in

def ker (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (v : GA E a) : ℂ :=
  if GeneralLinearGroup.map (pFin E) v ∈ U then β (toL (GeneralLinearGroup.map (pInf E) v).val) else 0

def tst (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (y : GA E a) : ℂ := ker U β y⁻¹

structure IsTest (β : Lie E a → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ β
  compact : HasCompactSupport β
  support : tsupport β ⊆ invSet E a

def ConjInv (β : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a), β (toL (k.1 * Matrix.of x * star k.1)) = β x

def dTest (X : Lie E a) (β : Lie E a → ℂ) (w : Lie E a) : ℂ :=
  fderiv ℝ β w (toL (Matrix.of w * Matrix.of X))

end GlobalTheory.CompanionTheory.SmoothRep
