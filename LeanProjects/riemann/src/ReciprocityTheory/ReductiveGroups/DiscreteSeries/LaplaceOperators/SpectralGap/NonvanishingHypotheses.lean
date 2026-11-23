import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CasOnLowStatement

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NonvanishingHypotheses (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) : Prop :=
  1 ≤ k ∧ Even k ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    Formalism.QuantumDeterminants.IsHCParam u ∧ Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) ∧
    Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b ∧ Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b ∧
    Formalism.MainNotions.CayleySignature.LowGapGe h r b ∧
    GapLap (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h

def NVConcl (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) {Vp : Type*} [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μG ν : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  ∃ W : Mat k r → Vp,
    AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
    Formalism.MainNotions.S.IsSPsiEquiv z (Formalism.MainNotions.S.psiGen k r z c) π W ∧ Formalism.MainNotions.S.l2SG ν W < ⊤ ∧
    Formalism.MainNotions.S.l2SG ν W ≠ 0 ∧
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), Formalism.MainNotions.S.rconv μG (Formalism.MainNotions.S.eFun μG σ w) W x = W x

def NVHStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ), NonvanishingHypotheses k r z c u v b h →
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ₀ : Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ₀ ∧
    ∀ w₀ : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ₀ w₀ →
    ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
      (π : Mat k r → (Vp →L[ℂ] Vp)), Formalism.MainNotions.S.IsHCTypeW k r z u π →
    ∀ μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r),
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
      Formalism.MainNotions.S.IsQuotMeas μG μS ν → NVConcl k r z c σ₀ w₀ π μG ν

def DSUnivStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, GapLap ε lam h →
  ∀ (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁))
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)),
    Formalism.MainNotions.S.IsDS ε lam σ₁ → Formalism.MainNotions.S.IsDS ε lam σ₂ →
  ∀ w₁ : H₁, Formalism.MainNotions.S.IsLowUnit ε lam σ₁ w₁ →
    ∃ w₂ : H₂, Formalism.MainNotions.S.IsLowUnit ε lam σ₂ w₂ ∧
      ∀ g ∈ Formalism.MainNotions.S.UJset ε, ⟪w₂, σ₂ g w₂⟫_ℂ = ⟪w₁, σ₁ g w₁⟫_ℂ

def CasDatumStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, GapLap ε lam h →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ →
  ∃ (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D),
    IsDerivedOn ε σ D E ∧ IsInfUnitary ε E ∧ IsKIrrHW ε E (lowK ε lam) V ∧
    (∀ k ∈ Kset ε, ∀ x ∈ V, ∃ y ∈ V, (y : H) = σ k (x : H)) ∧
    (∀ x ∈ V, casimir E x = (casVal lam : ℂ) • x) ∧
    ∀ x : H, x ∈ Formalism.MainNotions.S.lowKSub ε lam σ ↔ ∃ y : D, y ∈ V ∧ (y : H) = x

def DerivedLowStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, GapLap ε lam h →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ →
  ∃ (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D),
    IsDerivedOn ε σ D E ∧ IsInfUnitary ε E ∧ IsKIrrHW ε E (lowK ε lam) V ∧
    (∀ k ∈ Kset ε, ∀ x ∈ V, ∃ y ∈ V, (y : H) = σ k (x : H)) ∧
    (∀ x : D, x ∈ V → (x : H) ∈ Formalism.MainNotions.S.lowKSub ε lam σ) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ D), IsKIrrHW ε E μ S →
      Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map D.subtype)

def GapBigLapStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), Formalism.MainNotions.CayleySignature.RealPlaceNumericalSetting k r z c u v b → ∃ h : ℝ, NonvanishingHypotheses k r z c u v b h

def CayleyIndepStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (P₀ P : Mat k r), Formalism.MainNotions.S.IsCayleyU k r ε P₀ → Formalism.MainNotions.S.IsCayleyU k r ε P →
    Formalism.MainNotions.S.IsDS ε lam (fun g => σ (P₀⁻¹ * g * P₀)) →
    Formalism.MainNotions.S.IsDS ε lam (fun g => σ (P⁻¹ * g * P)) ∧
      Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (P⁻¹ * g * P)) = Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (P₀⁻¹ * g * P₀))

def NVTransferStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (H₀ : Type) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] (σ₀ : Mat k r → (H₀ →L[ℂ] H₀)) (w₀ : H₀)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (w : H)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp))
    (μG ν : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    σ₀ 1 = 1 → σ 1 = 1 →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ⟪w, σ g w⟫_ℂ = ⟪w₀, σ₀ g w₀⟫_ℂ) →
    NVConcl k r z c σ₀ w₀ π μG ν → NVConcl k r z c σ w π μG ν

def BAtTargetStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ), NonvanishingHypotheses k r z c u v b h →
    BesselAll (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) u

def NVHOfBStatement : Prop := BAtTargetStatement → NVHStatement

def BridgeStatement : Prop :=
  NVHStatement → ∀ (D : Formalism.BasicNotions.D7) (C : ℝ), Formalism.MainNotions.CayleySignature.Conclusion2 D C

def FamilyGapImplication : Prop :=
  NVHStatement → ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ), Formalism.MainNotions.CayleySignature.DeterminantValueFamily Fm C

end ReciprocityTheory.ChartRestriction.DS.Lap
