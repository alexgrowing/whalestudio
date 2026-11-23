import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureProductGroups
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_product_groups : ∀ (N A B : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
    (Ψ : A × B ≃ₜ N) (ω : A → A → B), Continuous (fun p : A × A => ω p.1 p.2) →
    (∀ a b a' b', Ψ (a, b) * Ψ (a', b') = Ψ (a + a', b + b' + ω a a')) →
    ∀ (φ : N ≃ₜ* N) (L₁ : A ≃ₜ+ A) (L₂ : B ≃ₜ+ B), (∀ a b, φ (Ψ (a, b)) = Ψ (L₁ a, L₂ b)) →
      mulEquivHaarChar φ = addEquivAddHaarChar L₁ * addEquivAddHaarChar L₂ := by
  first | exact @GlobalTheory.mulEquivHaarChar_heisenberg_chart | exact GlobalTheory.mulEquivHaarChar_heisenberg_chart | (intros; apply GlobalTheory.mulEquivHaarChar_heisenberg_chart <;> assumption)
