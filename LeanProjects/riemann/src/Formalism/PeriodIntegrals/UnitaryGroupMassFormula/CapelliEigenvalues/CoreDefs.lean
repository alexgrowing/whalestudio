import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.SmRight

open Matrix PI.UpqRep

noncomputable section

namespace PI.UnitaryGroupMassFormula.CapelliEig

def CapTransport : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H P Q : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E) (u : ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → P * Q = 1 → H = Pᴴ * Formalism.REAL.Jm ε * P →
    Formalism.REAL.SmoothOnGV ε (fun x => F (Q * x * P)) → Formalism.QuantumDeterminants.inUH H g →
    Formalism.QuantumDeterminants.capelliH H u F g = Formalism.QuantumDeterminants.capelli ε u (fun x => F (Q * x * P)) (P * g * Q)

def FunAct : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    IsDS ε lam σ → ∀ (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs),
    (∀ w, Q w ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ) →
    ∀ (u : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g → ∀ w : Wq,
      Formalism.QuantumDeterminants.capelli ε u (fun x => P.comp ((σ x).comp Q)) g w =
        P (σ g (PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) (Q w)))

def SmTrans : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (P₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsCayleyU k r ε P₀ →
    ∀ (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs), (∀ w, Q w ∈ smoothVecs (k := k) (r := r) σ) →
      (∀ w, Q w ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun x => σ (P₀⁻¹ * x * P₀))) ∧
      Formalism.REAL.SmoothOnGV ε (fun x => P.comp ((σ (P₀⁻¹ * x * P₀)).comp Q))

end PI.UnitaryGroupMassFormula.CapelliEig

end
