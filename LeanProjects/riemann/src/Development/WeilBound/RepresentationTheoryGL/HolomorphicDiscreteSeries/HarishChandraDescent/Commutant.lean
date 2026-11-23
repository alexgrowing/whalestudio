import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

def ForRep (Q : ∀ {n : ℕ} (_ : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) ρ → Q ε ρ

def Commutant : Prop := ForRep fun ε H _ _ _ ρ => ∀ T : H →L[ℂ] H, (∀ g ∈ UJset ε, Commute T (ρ g)) →
  ∃ T' : Module.End ℂ (smD ε ρ), (∀ x, (T' x : H) = T x) ∧ ∀ a b x, T' (smE ε ρ a b x) = smE ε ρ a b (T' x)

def AdEq : Prop := ForRep fun ε H _ _ _ ρ => ∀ g ∈ UJset ε, ∃ T' : Module.End ℂ (smD ε ρ), (∀ x, (T' x : H) = ρ g x) ∧
  ∀ X x, T' (actM (smE ε ρ) X x) = actM (smE ε ρ) (g * X * g⁻¹) (T' x)

def CasAd : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
  (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g.det →
    ∑ a, ∑ b, actM E (g * Matrix.single a b 1 * g⁻¹) * actM E (g * Matrix.single b a 1 * g⁻¹) = casimir E

def IntWt : Prop := ForRep fun {n} ε _ _ _ _ ρ => ∀ (ν : Fin n → ℝ) (x : smD ε ρ), x ≠ 0 → IsWt (smE ε ρ) ν x →
  ∀ a, ∃ m : ℤ, ν a = m

def HCOf : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (L : Fin n → ℝ) (h : ℝ), (∀ a, ∃ m : ℤ, L a = m) → 0 < h →
  (∀ a b, a < b → h + 2 * n ≤ L a - L b) → ∃ mu : Fin n → ℝ, Formalism.QuantumDeterminants.IsHCParam mu ∧ lowK ε mu = L ∧
    GapAtLeast ε mu h ∧ ∀ a, |mu a - L a| ≤ n

def Cut : Prop := ForRep fun {n} ε H _ _ _ ρ => Dense (smD ε ρ : Set H) → ∀ (ν : Fin n → ℝ) (κ S : ℝ) (y : smD ε ρ), 0 < S →
  Good ε (smE ε ρ) ν κ y → κ * ‖y‖ ^ 2 - (⟪casimir (smE ε ρ) y, y⟫_ℂ).re ≤ S * ‖y‖ ^ 2 →
    ∃ N : Submodule ℂ (smD ε ρ), Stab (smE ε ρ) N ∧
      (∀ x ∈ N, (κ - 2 * S) * ‖x‖ ^ 2 ≤ (⟪casimir (smE ε ρ) x, x⟫_ℂ).re) ∧ ∃ y' ∈ N, Good ε (smE ε ρ) ν κ y'

def Ident : Prop := ForRep fun {n} ε H _ _ _ ρ => ∀ (mu : Fin n → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam mu → GapAtLeast ε mu h →
  (n : ℝ) ^ 3 + 2 * n + 1 < h → ∀ V : Submodule ℂ (smD ε ρ), IsKIrrHW ε (smE ε ρ) (lowK ε mu) V →
  NoDown ε (smE ε ρ) (lowK ε mu) V → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε mu σ →
      ∃ j : H' →L[ℂ] H, j ≠ 0 ∧ ∀ g ∈ UJset ε, ∀ x, j (σ g x) = ρ g (j x)

def DSData : Prop := ForRep fun {n} ε H _ _ _ π => ∀ (lam : Fin n → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam → GapAtLeast ε lam h →
  (n : ℝ) ^ 3 + 2 * n + 1 < h → Formalism.MainNotions.S.IsDS ε lam π →
    (∀ x : smD ε π, casimir (smE ε π) x = (casVal lam : ℂ) • x) ∧
    (∃ v : smD ε π, ‖v‖ = 1 ∧ IsKHWVec ε (smE ε π) (lowK ε lam) v) ∧
    ∀ (x : H) (δ : ℝ), 0 < δ → ∃ f : smD ε π, KFin ε (smE ε π) f ∧ ‖x - f‖ < δ

def Core : Prop := ForRep fun {n} ε H _ _ _ ρ => Dense (smD ε ρ : Set H) → ∀ (μ : Fin n → ℝ) (S τ : ℝ) (J : ℕ) (x : smD ε ρ),
  0 < S → x ≠ 0 → KFin ε (smE ε ρ) x → qf (smE ε ρ) μ x ≤ S * ‖x‖ ^ 2 → (∀ a b, a < b → τ ≤ μ a - μ b) →
  2 * S < J * (2 * (τ - 2 * (Real.sqrt (2 * S) + J)) - 2 * n - 2) →
  (n : ℝ) ^ 3 + 4 * n + 2 + 2 * (Real.sqrt (2 * S) + J) ≤ τ →
    ∃ mu : Fin n → ℝ, Formalism.QuantumDeterminants.IsHCParam mu ∧ (∀ a, |mu a - μ a| ≤ Real.sqrt (2 * S) + J + n) ∧
      ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε mu σ →
          ∃ j : H' →L[ℂ] H, j ≠ 0 ∧ ∀ g ∈ UJset ε, ∀ x, j (σ g x) = ρ g (j x)

end PositivityTheory.RgHe3
