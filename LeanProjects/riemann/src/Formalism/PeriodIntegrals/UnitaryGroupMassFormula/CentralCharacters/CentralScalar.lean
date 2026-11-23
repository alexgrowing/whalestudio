import Formalism.PeriodIntegrals.DSInfCharCap

noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

abbrev Sm {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ

def SmSub : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    (0 : H) ∈ Sm ε σ ∧ (∀ v ∈ Sm ε σ, ∀ w ∈ Sm ε σ, v + w ∈ Sm ε σ) ∧
      ∀ (c : ℂ), ∀ v ∈ Sm ε σ, c • v ∈ Sm ε σ

def SmStable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    ∀ (Y : Matrix (Fin n) (Fin n) ℂ), ∀ v ∈ Sm ε σ, dsigC ε σ Y v ∈ Sm ε σ

def DLinV : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    ∀ (Y : Matrix (Fin n) (Fin n) ℂ),
      (∀ v ∈ Sm ε σ, ∀ w ∈ Sm ε σ, dsigC ε σ Y (v + w) = dsigC ε σ Y v + dsigC ε σ Y w) ∧
      ∀ (c : ℂ), ∀ v ∈ Sm ε σ, dsigC ε σ Y (c • v) = c • dsigC ε σ Y v

def DLinY : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    ∀ v ∈ Sm ε σ,
      (∀ Y Z : Matrix (Fin n) (Fin n) ℂ, dsigC ε σ (Y + Z) v = dsigC ε σ Y v + dsigC ε σ Z v) ∧
      ∀ (c : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), dsigC ε σ (c • Y) v = c • dsigC ε σ Y v

def DBracket : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    ∀ v ∈ Sm ε σ, ∀ Y Z : Matrix (Fin n) (Fin n) ℂ,
      dsigC ε σ Y (dsigC ε σ Z v) - dsigC ε σ Z (dsigC ε σ Y v) = dsigC ε σ (Y * Z - Z * Y) v

def AdEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    ∀ g ∈ PI.UpqRep.UJset ε, ∀ v ∈ Sm ε σ, σ g v ∈ Sm ε σ ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℂ, σ g (dsigC ε σ Y v) = dsigC ε σ (g * Y * g⁻¹) (σ g v)

def SkewAdj : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    ∀ v ∈ Sm ε σ, ∀ w ∈ Sm ε σ, ∀ Y : Matrix (Fin n) (Fin n) ℂ,
      ⟪dsigC ε σ Y v, w⟫_ℂ = ⟪v, dsigC ε σ (Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε) w⟫_ℂ

def QdetConjInv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit g → ∀ u : ℂ,
      Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (g c a * g⁻¹ b d) • E c d) u = Formalism.REAL.qdet E u

def SchurGraph : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ →
    PI.UpqRep.IsIrredOn (PI.UpqRep.UJset ε) σ →
    ∀ (S : Submodule ℂ H) (T T' : H → H),
      (∀ v ∈ S, ∀ w ∈ S, T (v + w) = T v + T w) → (∀ (c : ℂ), ∀ v ∈ S, T (c • v) = c • T v) →
      (∀ g ∈ PI.UpqRep.UJset ε, ∀ v ∈ S, σ g v ∈ S ∧ T (σ g v) = σ g (T v)) →
      (∀ v ∈ S, ∀ w ∈ S, ⟪T v, w⟫_ℂ = ⟪v, T' w⟫_ℂ) →
      ∃ c : ℂ, ∀ v ∈ S, T v = c • v

def CentralScalar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsDS ε lam σ →
    ∀ u : ℂ, ∃ c : ℂ, ∀ v ∈ Sm ε σ, actU ε σ (Formalism.REAL.qdet (Egl n) u) v = c • v

def DSValue : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
    ∀ Y : ℂ, ∃ v ∈ Sm ε σ, v ≠ 0 ∧
      actU ε σ (Formalism.REAL.qdet (Egl n) (Y + ((n : ℂ) - 1) / 2)) v = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

end PI.UnitaryGroupMassFormula.DSIC
