import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReproducingIdentityExtendsHarishChandraSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reproducingIdentity_extends_harishChandraSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ),
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a →
    (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) →
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  first | exact @GlobalTheory.HCF.repro_span | exact GlobalTheory.HCF.repro_span | (intros; apply GlobalTheory.HCF.repro_span <;> assumption)
