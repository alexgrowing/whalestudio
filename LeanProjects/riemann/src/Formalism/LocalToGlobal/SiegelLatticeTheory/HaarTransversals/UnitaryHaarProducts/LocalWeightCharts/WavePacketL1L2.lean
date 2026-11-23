import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk

abbrev Gr (k r : ℕ) : Set (Mat k r) := Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

def mulP {k r : ℕ} (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r :=
  fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

section Defs

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

def bInt (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (w' : H) (ξ : Vp) (v : H)
    (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp :=
  (⟪w', σ (Matrix.of p.1 * Matrix.of p.2) v⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
    π (Matrix.of p.1)⁻¹ ξ

def B0 (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (w' : H) (ξ : Vp) (v : H) : Vp :=
  ∫ p, bInt z c σ π w' ξ v p ∂(μW.prod μN)

def Af (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (w : H) (x₀ : Mat k r) (ξ : Vp)
    (g : Mat k r) : Vp :=
  B0 z c σ π μW μN (σ x₀ w) ξ (σ g w)

def Wf (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (g : Mat k r) : Vp :=
  ((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℂ) • A g

def bOp (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (w : H) (x₀ x : Mat k r) :
    Vp →L[ℂ] Vp :=
  ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
      π (Matrix.of p.1)⁻¹ ∂(μW.prod μN)

def Hyp (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H)
    (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  RealPlaceNumericalSetting k r z c u v b ∧ IsDSHpk k r (eps48 k r) (lam48 k r v b) σ ∧ IsHCTypeW k r z u π ∧
    IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w ∧
    IsHaarOn (Gr k r) μG ∧ IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS ∧ IsQuotMeas μG μS ν ∧
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧ IsFiniteMeasure μW ∧
    ∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤

end Defs

def HaarWN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    ∃ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧
      IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧ IsFiniteMeasure μW ∧
      ∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤

def SGrp : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.UWset k r z ⊆ Gr k r ∧ Formalism.QuantumDeterminants.Nset k r ⊆ Gr k r ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z,
      h * h' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ h⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ h * h⁻¹ = 1) ∧
    (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧
      m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ m * m⁻¹ = 1 ∧
      psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m' ∧ ‖psiGen k r z c m‖ = 1) ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r,
      h⁻¹ * m * h ∈ Formalism.QuantumDeterminants.Nset k r ∧ psiGen k r z c (h⁻¹ * m * h) = psiGen k r z c m)

def PiUnit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)), Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z → IsHCTypeW k r z u π →
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π ∧ ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ ξ : Vp, ‖π h ξ‖ = ‖ξ‖

def SigmaG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → IsURepOn (Gr k r) σ

def SProd : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    ∃ cS : ℝ≥0∞, cS ≠ 0 ∧ cS ≠ ⊤ ∧ (μW.prod μN).map mulP = cS • μS

def Decay : Prop :=
  CoefWeightedLoc → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ *
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤

def SchurG : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    ∃ d : ℝ, 0 < d ∧ ∀ v₁ w₁ v₂ w₂ : H,
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
        ⟪w₁, σ (Matrix.of g) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of g) v₂⟫_ℂ) μG ∧
      ∫ g, ⟪w₁, σ (Matrix.of g) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of g) v₂⟫_ℂ ∂μG =
        ⟪v₂, v₁⟫_ℂ * ⟪w₁, w₂⟫_ℂ / (d : ℂ)

def ReprodG : Prop :=
  Formalism.L2.SG.HCReprodM.HCReprodDSm → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    ∃ (α : Mat k r → ℂ) (Ω : Set (Mat k r)) (a : ℝ), IsCompact Ω ∧ Ω ⊆ Gr k r ∧
      Measurable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g)) ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g) • σ (Matrix.of g) w) μG ∧
      ∫ g, α (Matrix.of g) • σ (Matrix.of g) w ∂μG = w

def NIntDecay : Prop :=
  ∀ (k r : ℕ) (μN : Measure (Formalism.QuantumDeterminants.Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤) →
    ∫⁻ m, ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of m) ^ (-N1H k r)) ∂μN < ⊤

def AInt : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    ∀ g ∈ Gr k r, Integrable (bInt z c σ π (σ x₀ w) ξ (σ g w)) (μW.prod μN)

def AEquiv : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    IsSPsiEquiv z (psiGen k r z c) π (Af z c σ π μW μN w x₀ ξ)

def ACont : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    ContinuousOn (Af z c σ π μW μN w x₀ ξ) (Gr k r)

def AKind : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    ∀ x ∈ Gr k r,
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • (Af z c σ π μW μN w x₀ ξ) (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) (Af z c σ π μW μN w x₀ ξ) x = (Af z c σ π μW μN w x₀ ξ) x

def AReprod : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    ∃ (α : Mat k r → ℂ) (Ω : Set (Mat k r)) (a : ℝ), IsCompact Ω ∧ (1 : Mat k r) ∈ Ω ∧ Ω ⊆ Gr k r ∧
      Measurable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g)) ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x ∈ Gr k r,
        Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g) • (Af z c σ π μW μN w x₀ ξ) (x * Matrix.of g)) μG ∧
        rconv μG α (Af z c σ π μW μN w x₀ ξ) x = (Af z c σ π μW μN w x₀ ξ) x

def WavePacketL1L2 : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    ∫⁻ x, ‖(Af z c σ π μW μN w x₀ ξ) (Matrix.of x)‖ₑ ∂ν < ⊤ ∧ l2SG ν (Af z c σ π μW μN w x₀ ξ) < ⊤

def AWeighted : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    ∫⁻ x, ‖(Af z c σ π μW μN w x₀ ξ) (Matrix.of x)‖ₑ * ENNReal.ofReal (nuH k r z (Matrix.of x) ^ N1H k r) ∂ν < ⊤

def ANonzero : Prop :=
  BesselNVGap → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc →
    ∃ x₀ ∈ Gr k r, ∃ ξ : Vp, l2SG ν (Af z c σ π μW μN w x₀ ξ) ≠ 0

def ABound : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r, ∀ ξ : Vp,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ Gr k r,
      ∫⁻ p, ‖bInt z c σ π (σ x₀ w) ξ (σ g w) p‖ₑ ∂(μW.prod μN) ≤
        ENNReal.ofReal (C * Formalism.L2.SG.WuDecay.opn g ^ N1H k r)

end WlocSk
