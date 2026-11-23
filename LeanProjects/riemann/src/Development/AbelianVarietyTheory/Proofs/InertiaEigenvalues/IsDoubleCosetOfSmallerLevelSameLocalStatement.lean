import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocal
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local : ∀ {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G), J' ≤ J → J ⊓ Lc ≤ J' → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y) → x ∈ Lc → (∀ a ∈ A, a ∈ Lc) → Bridge.IsDC J x A → Bridge.IsDC J' x A := by
  first | exact @GlobalTheory.isDC_of_smaller_level_same_local | exact GlobalTheory.isDC_of_smaller_level_same_local | (intros; apply GlobalTheory.isDC_of_smaller_level_same_local <;> assumption)
