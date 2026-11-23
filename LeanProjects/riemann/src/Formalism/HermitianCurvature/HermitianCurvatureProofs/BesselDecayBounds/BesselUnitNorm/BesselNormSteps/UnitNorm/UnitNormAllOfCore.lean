import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.UnitNorm

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace PI.WUN

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.UnitNorm

def bInt {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r)
    (x : (Mt k r × Mt k r) × (Mt k r × Mt k r)) : L.Wq →L[ℂ] L.Wp :=
  (psi k r L.z L.c (Matrix.of x.1.2) * star (psi k r L.z' L.c (Matrix.of x.2.2))) •
    ((L.π (Matrix.of x.1.1)).comp
      ((F ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 * Matrix.of x.2.1)).comp
        (L.π' (Matrix.of x.2.1)⁻¹)))

def bMeas {k r : ℕ} (L : LocBessel k r) : Measure ((Mt k r × Mt k r) × (Mt k r × Mt k r)) :=
  (L.μW.prod L.μN).prod (L.μW'.prod L.μN)

theorem J_eq {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (g : Mx k r) :
    L.J F g = ∫ x, bInt L F g x ∂(bMeas L) := rfl

def DomAt {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q₀ : (Fin r → ℂ) × ℂ) : Prop :=
  ∃ U ∈ 𝓝 q₀, ∃ G : (Mt k r × Mt k r) × (Mt k r × Mt k r) → ℝ, Integrable G (bMeas L) ∧
    ∀ q ∈ U, AEStronglyMeasurable (bInt L F (bigCell k r q.1 (μsec q.2))) (bMeas L) ∧
      ∀ᵐ x ∂(bMeas L), ‖bInt L F (bigCell k r q.1 (μsec q.2)) x‖ ≤ G x

def FinStep (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Mx D.R.k D.R.rS → (H →L[ℂ] H)), IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) σ' →
    ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
    ∀ q₀ : (Fin D.R.rS → ℂ) × ℂ, InBig L q₀ → L.J f' (bigCell D.R.k D.R.rS q₀.1 (μsec q₀.2)) ≠ 0 →
      jNorm2 L f' μsec ≠ ⊤

def DomStep (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ' : Mx D.R.k D.R.rS → (H →L[ℂ] H)), IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) σ' →
    ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
    ∀ q₀ : (Fin D.R.rS → ℂ) × ℂ, InBig L q₀ → L.J f' (bigCell D.R.k D.R.rS q₀.1 (μsec q₀.2)) ≠ 0 →
      DomAt L f' μsec q₀

def CoreStep : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    IsSection k r L.z L.z' μsec →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
      (σ' : Mx k r → (H →L[ℂ] H)), IsDSHpk k r ε lam σ' →
    ∀ f' : Mx k r → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH σ' f' →
    ∀ q₀ : (Fin r → ℂ) × ℂ, InBig L q₀ → L.J f' (bigCell k r q₀.1 (μsec q₀.2)) ≠ 0 →
      DomAt L f' μsec q₀ → jNorm2 L f' μsec ≠ 0

end PI.WUN
