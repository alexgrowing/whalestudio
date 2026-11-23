import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.UnitaryDecomposition PositivityTheory.RgHe

def res {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H) :=
  fun h => π (emb e h)

def Restrict : Prop := ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (H : Type)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)),
  Fits ε ε' e → IsURepOn (UJset ε) π → IsURepOn (UJset ε') (res e π) ∧
    ∃ I : smD ε π →ₗ[ℂ] smD ε' (res e π), (∀ x, (I x : H) = x) ∧
      ∀ a b x, I (smE ε π (e (Sum.inl a)) (e (Sum.inl b)) x) = smE ε' (res e π) a b (I x)

def Over {n : ℕ} {ε : Fin (n + 1) → Bool} (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (g : Formalism.REAL.UJ ε) : Prop :=
  ∀ Y, trace (dg d * (um g⁻¹ * blk0 e Y * um g)) = trace (dg d' * Y)

def Mom2 : Prop := ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (lam d : Fin (n + 1) → ℝ)
  (d' : Fin n → ℝ) (g : Formalism.REAL.UJ ε), Over e d d' g → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ (H : Type)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)),
  IsURepOn (UJset ε) π → ∀ v : smD ε π, ‖v‖ = 1 → IsKHWVec ε (smE ε π) (lowK ε (lam + t • d)) v →
  casimir (smE ε π) v = (casVal (lam + t • d) : ℂ) • v → ∃ η : smD ε π, ‖η‖ = 1 ∧
    ∑ a, ∑ b, ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) η - (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • η‖ ^ 2 ≤ C * t

def Trial : Prop := ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
  (lam d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g : Formalism.REAL.UJ ε), Fits ε ε' e → Over e d d' g → ∃ C : ℝ, 0 < C ∧
  ∀ t : ℝ, 1 ≤ t → Formalism.QuantumDeterminants.IsHCParam (lam + t • d) → GapAtLeast ε (lam + t • d) (200 * ((n : ℝ) + 1) ^ 3) → ∀ (H : Type)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)),
  Formalism.MainNotions.S.IsDS ε (lam + t • d) π → IsURepOn (UJset ε') (res e π) ∧ Dense (smD ε' (res e π) : Set H) ∧
    ∃ x : smD ε' (res e π), x ≠ 0 ∧ KFin ε' (smE ε' (res e π)) x ∧ qf (smE ε' (res e π)) (t • d') x ≤ C * t * ‖x‖ ^ 2

def Far : Prop := ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
  (lam d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g : Formalism.REAL.UJ ε), Fits ε ε' e → Over e d d' g →
  (∀ a b, a < b → 1 ≤ d' a - d' b) → ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → Formalism.QuantumDeterminants.IsHCParam (lam + t • d) →
  GapAtLeast ε (lam + t • d) (200 * ((n : ℝ) + 1) ^ 3) → ∀ (H : Type)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)),
  Formalism.MainNotions.S.IsDS ε (lam + t • d) π → ∃ mu : Fin n → ℝ, Formalism.QuantumDeterminants.IsHCParam mu ∧ (∀ a, |mu a - t * d' a| ≤ C * Real.sqrt t) ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε' mu σ → ∃ j : H' →L[ℂ] H, j ≠ 0 ∧ IsHMap ε' e π σ j

end PositivityTheory.RgHe3
