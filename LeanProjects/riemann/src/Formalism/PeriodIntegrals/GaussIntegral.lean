import Mathlib

open ValuativeRel MeasureTheory

namespace PI

def GaussIntegral : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) F), H.IsSymm → H.det ≠ 0 →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, t ≠ 0 → (μ ((fun y => t * y) '' (𝒪[F] : Set F))).toReal < δ →
    ‖∫ x in (L : Set (Fin d → F)), ψ (dotProduct x (H.mulVec x) / (2 * t))
        ∂(Measure.pi fun _ : Fin d => μ)‖ =
      (μ ((fun y => (t⁻¹ • H).det * y) '' (𝒪[F] : Set F))).toReal ^ (-(1 / 2 : ℝ))

end PI
