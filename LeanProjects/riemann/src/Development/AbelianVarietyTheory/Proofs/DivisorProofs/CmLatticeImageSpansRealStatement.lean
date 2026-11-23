import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageSpansReal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_image_spans_real : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) →
      Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ := by
  first | exact @GlobalTheory.CMSpan.span_real_eq_top | exact GlobalTheory.CMSpan.span_real_eq_top | (intros; apply GlobalTheory.CMSpan.span_real_eq_top <;> assumption)
