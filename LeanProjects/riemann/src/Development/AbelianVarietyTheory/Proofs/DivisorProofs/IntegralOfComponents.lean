import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSec

noncomputable section

namespace GlobalTheory.ConeEulerGen

open MeasureTheory Filter Topology

theorem integral_of_components {G A : Type} {ι : Type} [Fintype ι] {B : ι → Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] [∀ i, Group (B i)] [∀ i, TopologicalSpace (B i)] [∀ i, IsTopologicalGroup (B i)]
    [∀ i, LocallyCompactSpace (B i)] [∀ i, SecondCountableTopology (B i)] [∀ i, T2Space (B i)]
    [∀ i, MeasurableSpace (B i)] [∀ i, BorelSpace (B i)]
    (μ : Measure G) [μ.IsHaarMeasure] (μA : Measure A) [μA.IsHaarMeasure] (μB : ∀ i, Measure (B i))
    [∀ i, (μB i).IsHaarMeasure]
    (πA : G →* A) (hπA : Continuous πA) (πB : ∀ i, G →* B i) (hπB : ∀ i, Continuous (πB i))
    (jA : A → G) (hjA : Continuous jA) (jB : ∀ i, B i → G) (hjB : ∀ i, Continuous (jB i))
    (hAA : ∀ a, πA (jA a) = a) (hAB : ∀ i b, πA (jB i b) = 1) (hBA : ∀ i a, πB i (jA a) = 1)
    (hBB : ∀ i b, πB i (jB i b) = b) (hBB' : ∀ i i' b, i' ≠ i → πB i (jB i' b) = 1)
    (R : G → ℂ) (hRA : ∀ a x, R (jA a * x) = R x) (hRB : ∀ i b x, R (jB i b * x) = R x) :
    ∃ c : ℂ, ∀ (f : A → ℂ) (g : ∀ i, B i → ℂ),
      ∫ x, f (πA x) * (∏ i, g i (πB i x)) * R x ∂μ = c * ((∫ a, f a ∂μA) * ∏ i, ∫ b, g i b ∂μB i) := by
  first
  | exact @_root_.GlobalTheory.SectionProjectionFormula.main
  | exact _root_.GlobalTheory.SectionProjectionFormula.main
  | (apply _root_.GlobalTheory.SectionProjectionFormula.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SectionProjectionFormula.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SectionProjectionFormula.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SectionProjectionFormula.main ..)

end GlobalTheory.ConeEulerGen

end
