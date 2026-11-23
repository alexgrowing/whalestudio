import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Generic

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

def sM (p : Mt k r × Mt k r) : Mx k r := Matrix.of p.1 * Matrix.of p.2

def GHyp (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  (∃ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), IsHCParam lam ∧ IsDSHpk k r ε lam σ) ∧
    IsHaarOn (UH (Hpk k r)) μG ∧ (inWb k r z ∧ 0 < Tz k r z) ∧ (∃ u : Fin k → ℝ, IsHCTypeW k r z u π) ∧
    (IsHaarOn (UWset k r z) μW ∧ μW Set.univ = 1) ∧
    (∃ κ : ENNReal, 0 < κ ∧ κ ≠ ⊤ ∧ μN = haarLie (Nset k r) κ) ∧ IsQuotMeas μG (muSof μW μN) ν

def Aop (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) (y : Mx k r) : Wp →L[ℂ] Wp :=
  be z c π μW μN σ (σ y w) v

def Fg (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) (y : Mx k r) : ℂ :=
  ⟪v, σ y w⟫_ℂ * star (trW (Aop z c π μW μN σ w v y))

def SchurOn (μG : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
    ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def DIntAt (μW μN μG : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v ∈ smoothVecs (k := k) (r := r) σ, IsKFinHpk (k := k) (r := r) σ v →
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ‖⟪v, σ (Matrix.of q.1) w⟫_ℂ‖ * ‖⟪v, σ (sM q.2 * Matrix.of q.1) w⟫_ℂ‖) (μG.prod (μW.prod μN))

end Generic

def SchurH : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)),
    IsHCParam lam → IsDSHpk k r ε lam σ → IsHaarOn (UH (Hpk k r)) μG → SchurOn μG σ

def DInt (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq → DIntAt μW L.μN μG σ

def SmoothStep : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)), IsDSHpk k r ε lam σ →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ g ∈ UH (Hpk k r), σ g w ∈ smoothVecs (k := k) (r := r) σ

def FdegStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)), SchurOn μG σ → ∀ w : H, w ≠ 0 → 0 < fdegH μG σ w

def NuStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)), GHyp z π μW μN μG ν σ → ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk k r)

def WeilStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)), GHyp z π μW μN μG ν σ →
    ∀ F : Mx k r → ℂ, Integrable (fun x : Mt k r => F (Matrix.of x)) μG →
      (∀ᵐ x ∂ν, Integrable (fun p => F (sM p * Matrix.of x)) (μW.prod μN)) ∧
      Integrable (fun x : Mt k r => ∫ p, F (sM p * Matrix.of x) ∂(μW.prod μN)) ν ∧
      ∫ x, F (Matrix.of x) ∂μG = ∫ x, (∫ p, F (sM p * Matrix.of x) ∂(μW.prod μN)) ∂ν

def HSStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)), GHyp z π μW μN μG ν σ → ConvAt z c π μW μN σ →
    Cv.GrpF k r z → Cv.SigU σ → Cv.PiU z π → Cv.PsiF k r z c → Cv.MeasF z π μW μN →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v ∈ smoothVecs (k := k) (r := r) σ, IsKFinHpk (k := k) (r := r) σ v →
    ∀ x : Mx k r, x ∈ UH (Hpk k r) →
      Integrable (fun p => Fg z c π μW μN σ w v (sM p * x)) (μW.prod μN) ∧
      ((hsSq (Aop z c π μW μN σ w v x) : ℝ) : ℂ) = ∫ p, Fg z c π μW μN σ w v (sM p * x) ∂(μW.prod μN)

def FIntStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)), GHyp z π μW μN μG ν σ → ConvAt z c π μW μN σ →
    Cv.GrpF k r z → Cv.SigU σ → Cv.PiU z π → Cv.PsiF k r z c → Cv.MeasF z π μW μN → DIntAt μW μN μG σ →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v ∈ smoothVecs (k := k) (r := r) σ, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (fun x : Mt k r => Fg z c π μW μN σ w v (Matrix.of x)) μG

def GIntStep : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)), GHyp z π μW μN μG ν σ → ConvAt z c π μW μN σ →
    Cv.GrpF k r z → Cv.SigU σ → Cv.PiU z π → Cv.PsiF k r z c → Cv.MeasF z π μW μN → DIntAt μW μN μG σ →
    SchurOn μG σ →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, IsKFinHpk (k := k) (r := r) σ v →
      ∫ x, Fg z c π μW μN σ w v (Matrix.of x) ∂μG =
        ((‖w‖ ^ 2 : ℝ) : ℂ) * star (trW (be z c π μW μN σ v v)) / ((fdegH μG σ w : ℝ) : ℂ)

section Assembly

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

end Assembly

end PI.WBL.FSW
