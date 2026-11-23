import Mathlib
import Formalism.PeriodIntegrals.BesselL2FixAtZero

noncomputable section

namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero

open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep PI.BesselL2FixAtZero

def SchurVec : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
  ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w) μG ∧
    ∫ g, eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w ∂μG = σ x w

def BesselFun : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b → GapC 0 k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ ℓ : H →ₗ[ℂ] Vp,
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      ℓ (σ h (σ m (σ g w))) = psiGen k r z c m • π h (ℓ (σ g w))) ∧
    AEStronglyMeasurable (fun x => ℓ (σ (Matrix.of x) w)) μG ∧
    AEStronglyMeasurable (fun x => ℓ (σ (Matrix.of x) w)) ν ∧
    l2SG ν (fun g => ℓ (σ g w)) < ⊤ ∧ l2SG ν (fun g => ℓ (σ g w)) ≠ 0 ∧
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      ∫ g, eFun μG σ w (Matrix.of g) • ℓ (σ (x * Matrix.of g) w) ∂μG =
        ℓ (∫ g, eFun μG σ w (Matrix.of g) • σ (x * Matrix.of g) w ∂μG)

theorem uh_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  have e : (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, ha', hb']

theorem sigma_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {a b : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, _⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hinv1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hinv2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have conjmem : ∀ g : Mat k r, g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → P * g * P⁻¹ ∈ UJset ε := by
    intro g hg
    have hg0 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hPJ' : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hPJ
    have hg' : gᴴ * (Pᴴ * Jm ε * P) * g = Pᴴ * Jm ε * P := by rw [hPJ']; exact hg0
    show (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = Jm ε
    calc (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Jm ε * P) * g) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Jm ε * P) * P⁻¹ := by rw [hg']
      _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm ε := by rw [hinv2]; simp
  have e1 : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    have : P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    rw [this, hinv1, Matrix.one_mul, Matrix.mul_one]
  have e2 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
    have : P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, hinv1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hmul := hDS.2.2.1.1.2
  have h : σ (P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P) =
      (σ (P⁻¹ * (P * a * P⁻¹) * P)).comp (σ (P⁻¹ * (P * b * P⁻¹) * P)) :=
    hmul _ (conjmem a ha) _ (conjmem b hb)
  rw [e2, e1, e1, e1] at h
  exact h

end PI.UnitaryGroupMassFormula.BesselL2FixAtZero
