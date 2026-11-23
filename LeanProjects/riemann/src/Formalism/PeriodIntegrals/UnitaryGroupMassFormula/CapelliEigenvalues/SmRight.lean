import Formalism.PeriodIntegrals.CapelliEig
import Formalism.PeriodIntegrals.KFinSmooth
import Formalism.PeriodIntegrals.DSInfCharCap

open Matrix PI.UpqRep

noncomputable section

namespace PI.UnitaryGroupMassFormula.CapelliEig

def UHGrp : Prop :=
  ∀ (k r : ℕ), ∀ a ∈ UH (Hpk k r), IsUnit a ∧ a⁻¹ ∈ UH (Hpk k r) ∧ ∀ b ∈ UH (Hpk k r), a * b ∈ UH (Hpk k r)

def MulH : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)),
    IsDSHpk k r ε lam σ → ∀ x ∈ UH (Hpk k r), ∀ y ∈ UH (Hpk k r), σ (x * y) = (σ x).comp (σ y)

def SmRight : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs)),
    IsDSHpk k r ε lam σ → ∀ v : Hs, v ∈ smoothVecs (k := k) (r := r) σ →
    ∀ c ∈ UH (Hpk k r), σ c v ∈ smoothVecs (k := k) (r := r) σ

def Loc : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H P Q : Matrix (Fin n) (Fin n) ℂ) (F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E) (u : ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → P * Q = 1 → H = Pᴴ * Formalism.REAL.Jm ε * P →
    (∀ x, Formalism.QuantumDeterminants.inUH H x → F₁ x = F₂ x) → Formalism.QuantumDeterminants.inUH H g →
    Formalism.QuantumDeterminants.capelliH H u F₁ g = Formalism.QuantumDeterminants.capelliH H u F₂ g

def CoefSm : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs), (∀ w, Q w ∈ smoothVecs (k := k) (r := r) σ) →
    ∀ Y : ℂ, ∀ g ∈ UH (Hpk k r),
      PI.CapelliEig.capC (k := k) (r := r) Y (fun x => P.comp ((σ x).comp Q)) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • P.comp ((σ g).comp Q)

end PI.UnitaryGroupMassFormula.CapelliEig

end
