import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import Formalism.HermitianCurvature.StatementB

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0

open Formalism.QuantumDeterminants

def nS (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def q0S (k r : ℕ) : ℝ := ((min (k + r) (r + 1) : ℕ) : ℝ)

def bG (k r : ℕ) : ℝ := 2 * nS k r * q0S k r

def bS (k r : ℕ) : ℝ := 2 * (r : ℝ) * nS k r ^ 2

section Fdeg

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsFdegB (μG : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g : Mt k r => ⟪w, σ (Matrix.of g) v⟫_ℂ * star ⟪w', σ (Matrix.of g) v'⟫_ℂ) μG ∧
    ∫ g : Mt k r, ⟪w, σ (Matrix.of g) v⟫_ℂ * star ⟪w', σ (Matrix.of g) v'⟫_ℂ ∂μG =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

end Fdeg

def IntGStatement : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    ∀ b : ℝ, bG k r < b → Integrable (fun g : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of g) ^ (-b)) μG

def IntSStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    ∀ x₀ ∈ UH (Hpk k r), ∀ x ∈ UH (Hpk k r), ∀ b : ℝ, bS k r < b →
      Integrable (fun p : Mt k r × Mt k r =>
        Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) (μW.prod μN)

def FdegHEqStatement : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H))
    (w : H) (d : ℝ) (μG : Measure (Mt k r)), ‖w‖ = 1 → IsFdegB μG σ d → Formalism.MainNotions.S.fdegH μG σ w = d

def ReproCoreStatement : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d : ℝ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (z : Fin (2 * r + k + 1) → ℂ)
    (μG μW μN : Measure (Mt k r)) (x₀ x : Mat k r) (ξ : Vp),
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ → ‖w‖ = 1 → IsFdegB μG σ d →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Nset k r) μN → x₀ ∈ UH (Hpk k r) → x ∈ UH (Hpk k r) →
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      Formalism.MainNotions.S.eFun μG σ w (Matrix.of q.1) •
        (⟪w, σ (x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1))) w⟫_ℂ •
          chiInv ψ π (Matrix.of q.2.1) (Matrix.of q.2.2) ξ)) (μG.prod (μW.prod μN)) →
    Formalism.MainNotions.S.rconv μG (Formalism.MainNotions.S.eFun μG σ w) (sInt μW μN ψ π (fun g => ⟪w, σ (x₀⁻¹ * g) w⟫_ℂ) ξ) x =
      sInt μW μN ψ π (fun g => ⟪w, σ (x₀⁻¹ * g) w⟫_ℂ) ξ x

def ReproStatement : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d a C : ℝ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (μG μW μN : Measure (Mt k r)),
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ → ‖w‖ = 1 → IsFdegB μG σ d →
    (∀ g ∈ UH (Hpk k r), ‖⟪w, σ g w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN g ^ (-a)) →
    4 * max (bG k r) (bS k r) < a - 1 →
    inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsURepOn (UWset k r z) π →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    ∀ x₀ ∈ UH (Hpk k r), ∀ ξ : Vp, ∀ x ∈ UH (Hpk k r),
      Formalism.MainNotions.S.rconv μG (Formalism.MainNotions.S.eFun μG σ w)
                (sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π (fun g => ⟪w, σ (x₀⁻¹ * g) w⟫_ℂ) ξ) x =
        sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π (fun g => ⟪w, σ (x₀⁻¹ * g) w⟫_ℂ) ξ x

def NonzeroStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp))
    (μG μS ν : Measure (Mt k r)) (W : Mat k r → Vp),
    (∀ h ∈ UWset k r z, ∀ v : Vp, ‖π h v‖ = ‖v‖) →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG → Formalism.MainNotions.S.IsHaarOn (Sset k r z) μS →
    Formalism.MainNotions.S.IsQuotMeas μG μS ν →
    (∀ U : Set (Mt k r), IsOpen U → (∃ y ∈ U, Matrix.of y ∈ UH (Hpk k r)) → 0 < μG U) →
    ContinuousOn (fun y : Mt k r => W (Matrix.of y)) {y | Matrix.of y ∈ UH (Hpk k r)} →
    Formalism.MainNotions.S.IsSPsiEquiv z (Formalism.MainNotions.S.psiGen k r z c) π W →
    (∃ y ∈ UH (Hpk k r), W y ≠ 0) → Formalism.MainNotions.S.l2SG ν W ≠ 0

end ReciprocityTheory.ChartRestriction.DS.Lap.S0
