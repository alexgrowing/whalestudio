import Mathlib
import Formalism.PeriodIntegrals.GaussIntegral

open ValuativeRel MeasureTheory

noncomputable section

namespace PI.GI

def dual {F : Type} [Field F] (ψ : AddChar F ℂ) {d : ℕ} (L : Set (Fin d → F)) : Set (Fin d → F) :=
  {w | ∀ y ∈ L, ψ (dotProduct y w) = 1}

def md {F : Type} [Field F] [ValuativeRel F] [MeasurableSpace F] (μ : Measure F) (a : F) : ENNReal :=
  μ ((fun y => a * y) '' (𝒪[F] : Set F))

open scoped Classical in

def Orth : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (K : AddSubgroup (Fin d → F)), IsCompact (K : Set (Fin d → F)) → IsOpen (K : Set (Fin d → F)) →
  ∀ w : Fin d → F,
    ∫ y in (K : Set (Fin d → F)), ψ (dotProduct y w) ∂(Measure.pi fun _ : Fin d => μ) =
      if w ∈ dual ψ (K : Set (Fin d → F)) then (((Measure.pi fun _ : Fin d => μ) (K : Set (Fin d → F))).toReal : ℂ) else 0

def SqFormula : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) F), A.IsSymm →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
    ((‖∫ x in (L : Set (Fin d → F)), ψ (dotProduct x (A.mulVec x) / 2) ∂(Measure.pi fun _ : Fin d => μ)‖ ^ 2 : ℝ) : ℂ) =
      (((Measure.pi fun _ : Fin d => μ) (L : Set (Fin d → F))).toReal : ℂ) *
        ∫ z in {z | z ∈ (L : Set (Fin d → F)) ∧ A.mulVec z ∈ dual ψ (L : Set (Fin d → F))},
          ψ (dotProduct z (A.mulVec z) / 2) ∂(Measure.pi fun _ : Fin d => μ)

def SmallT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) F), H.IsSymm → H.det ≠ 0 →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, t ≠ 0 → (md μ t).toReal < δ →
    {z | z ∈ (L : Set (Fin d → F)) ∧ (t⁻¹ • H).mulVec z ∈ dual ψ (L : Set (Fin d → F))} =
        (fun w => (t • H⁻¹).mulVec w) '' dual ψ (L : Set (Fin d → F)) ∧
    ∀ z ∈ (L : Set (Fin d → F)), (t⁻¹ • H).mulVec z ∈ dual ψ (L : Set (Fin d → F)) →
      ψ (dotProduct z ((t⁻¹ • H).mulVec z) / 2) = 1

def DetScale : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (d : ℕ) (M : Matrix (Fin d) (Fin d) F), M.det ≠ 0 → ∀ S : Set (Fin d → F),
    (Measure.pi fun _ : Fin d => μ) ((fun w => M.mulVec w) '' S) = md μ M.det * (Measure.pi fun _ : Fin d => μ) S

def ModMul : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ a b : F, a ≠ 0 → b ≠ 0 → md μ (a * b) = md μ a * md μ b

def DualMeasure : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
    (Measure.pi fun _ : Fin d => μ) (L : Set (Fin d → F)) * (Measure.pi fun _ : Fin d => μ) (dual ψ (L : Set (Fin d → F))) = 1

end PI.GI
