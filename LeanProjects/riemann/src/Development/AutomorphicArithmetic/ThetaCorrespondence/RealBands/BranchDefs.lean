import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal
open scoped InnerProductSpace

namespace UpperTheory.Lit.Branch

def RealInputE : Prop := ∃ C : ℝ, 0 < C ∧ ForPair fun n e ε lam ε' _ B H H' _ _ _ _ π σ =>
  ∃ (v₀ v : H) (g₀ : Mat (n + 1)) (w' : H') (c : ℝ), IsLowUnit ε lam π v₀ ∧ g₀ ∈ UJset ε ∧ v = π g₀ v₀ ∧
    SmV (lieOf (Jm ε)) π v ∧ SmV (lieOf (Jm ε')) σ w' ∧ ‖w'‖ = 1 ∧ 0 < c ∧
    (∀ b : H', ∫ h, star ⟪v, π (embH e (umat h)) v⟫_ℂ * ⟪b, σ (umat h) w'⟫_ℂ ∂muG ε' = (c : ℂ) * (⟪w', w'⟫_ℂ * ⟪b, w'⟫_ℂ)) ∧
    (∀ g ∈ UJset ε, Integrable (fun h => ⟪v, π (g * embH e (umat h)) v⟫_ℂ) (muG ε') ∧
      ∫ h, ‖⟪v, π (g * embH e (umat h)) v⟫_ℂ‖ ∂muG ε' ≤ c * big C n B * colLen e g ^ (-(2 * (n : ℝ) + 7))) ∧
    (∀ X ∈ lieOf (Jm ε'), hsn X ≤ 1 → Integrable (fun h => ⟪dR π (embL e X) v, π (embH e (umat h)) v⟫_ℂ) (muG ε') ∧
      ∫ h, ‖⟪dR π (embL e X) v, π (embH e (umat h)) v⟫_ℂ‖ ∂muG ε' ≤ c * big C n B) ∧
    ∃ A : ℝ, ∀ g ∈ UJset ε, ‖⟪v, π g v⟫_ℂ‖ ≤ A * hsn g ^ (-(20 * ((n : ℝ) + 1) ^ 2))

def IsEmb {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (e : Option (Fin n) ≃ Fin (n + 1)) (ε' : Fin n → Bool) (π : Mat (n + 1) → (H →L[ℂ] H)) (σ : Mat n → (H' →L[ℂ] H'))
    (j : H' →L[ℂ] H) (P : H →L[ℂ] H') : Prop :=
  IsHMap e ε' π σ j ∧ (∀ w, ‖j w‖ = ‖w‖) ∧ ∀ v w, ⟪j w, v⟫_ℂ = ⟪w, P v⟫_ℂ

def ProjLarge : Prop := ForPair fun n e ε lam ε' _ B H H' _ _ _ _ π σ => ∀ v₀, IsLowUnit ε lam π v₀ →
  ∃ (j : H' →L[ℂ] H) (P : H →L[ℂ] H'), IsEmb e ε' π σ j P ∧ ∃ g₀ ∈ UJset ε,
    hsn g₀ ≤ (8 * ((n : ℝ) + 1) * B) ^ ((10 : ℝ) * ((n : ℝ) + 1)) ∧ 1 ≤ big 100 n B * ‖P (π g₀ v₀)‖

def EigMap : Prop := ForPair fun _ e _ _ ε' _ _ H H' _ _ _ _ π σ => ∀ d, IsFdeg (muG ε') σ d →
  ∀ w₀ : H', ‖w₀‖ = 1 → Integrable (fun h => ⟪w₀, σ (umat h) w₀⟫_ℂ) (muG ε') → ∀ j P, IsEmb e ε' π σ j P →
    ∀ v : H, Integrable (fun h => ⟪v, π (embH e (umat h)) v⟫_ℂ) (muG ε') → P v ≠ 0 →
      ∃ (w : H') (c : ℝ) (T : H →L[ℂ] H'), w ≠ 0 ∧ ‖P v‖ ^ 2 / (2 * d) ≤ c ∧
        (∀ b : H', ∫ h, star ⟪v, π (embH e (umat h)) v⟫_ℂ * ⟪b, σ (umat h) w⟫_ℂ ∂muG ε' = (c : ℂ) * ⟪b, w⟫_ℂ) ∧
        (∀ h ∈ UJset ε', ∀ x, T (π (embH e h) x) = σ h (T x)) ∧ T v = w

def MapSmooth : Prop := ForPair fun _ e ε _ ε' _ _ H H' _ _ _ _ π σ => ∀ T : H →L[ℂ] H',
  (∀ h ∈ UJset ε', ∀ x, T (π (embH e h) x) = σ h (T x)) → ∀ v, SmV (lieOf (Jm ε)) π v → SmV (lieOf (Jm ε')) σ (T v)

def VolDeg : Prop := ∃ C : ℝ, 0 < C ∧ ForPair fun n _ _ _ ε' _ B _ _ _ _ _ _ _ σ => ∀ d, IsFdeg (muG ε') σ d →
  (muG ε' (nbh ε' (1 / 4))).toReal ≤ big C n B / d

end UpperTheory.Lit.Branch

end
