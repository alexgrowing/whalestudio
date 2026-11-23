import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridMovedTensor_bounded_support_locallyConstant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  first | exact @GlobalTheory.MovedBound.moved_bounded_locConst | exact GlobalTheory.MovedBound.moved_bounded_locConst | (intros; apply GlobalTheory.MovedBound.moved_bounded_locConst <;> assumption)
