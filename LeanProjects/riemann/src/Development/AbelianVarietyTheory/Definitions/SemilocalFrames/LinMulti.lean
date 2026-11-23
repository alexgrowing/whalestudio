import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.BesselMapUniq

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Ell

open Formalism.MainNotions.S

section Rep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))

def SmV (w : H) : Prop :=
  ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ Lie) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w

def dR (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : H := deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) 0

def SobC (ℓ : H →ₗ[ℂ] ℂ) : Prop :=
  ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ Lie) ∧
    ∀ w, SmV Lie σ w → ‖ℓ w‖ ≤ C * (S.map fun l => ‖l.foldr (dR σ) w‖).sum

end Rep

def lieOf {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {X | Xᴴ * G + G * X = 0}

structure Mod (n k r : ℕ) where
  ε : Fin n → Bool
  lam : Fin n → ℝ
  H : Type
  [nH : NormedAddCommGroup H]
  [iH : InnerProductSpace ℂ H]
  σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)
  G : Matrix (Fin n) (Fin n) ℂ
  fr : Matrix (Fin n) (Fin n) ℂ
  Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ
  Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ
  z : Fin (2 * r + k + 1) → ℂ
  c : Fin r → ℂ
  u : Fin k → ℝ
  Vp : Type
  [nV : NormedAddCommGroup Vp]
  [iV : InnerProductSpace ℂ Vp]
  π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Vp →L[ℂ] Vp)
  hlam : Formalism.QuantumDeterminants.IsHCParam lam
  ds : IsDS ε lam σ
  fr_unit : IsUnit fr
  fr_gram : frᴴ * Formalism.REAL.Jm ε * fr = G
  Q_Qi : Q * Qi = 1
  Qi_Q : Qi * Q = 1
  Q_gram : Qᴴ * G * Q = Formalism.QuantumDeterminants.Hpk k r
  hz : Formalism.QuantumDeterminants.inWb k r z
  hT : 0 < Formalism.QuantumDeterminants.Tz k r z
  hc : ∀ a, c a ≠ 0
  hπ : IsHCTypeW k r z u π

attribute [instance] Mod.nH Mod.iH Mod.nV Mod.iV

namespace Mod

variable {n k r : ℕ} (M : Mod n k r)

def rep (g : Matrix (Fin n) (Fin n) ℂ) : M.H →L[ℂ] M.H := M.σ (M.fr * g * M.fr⁻¹)

def Sm (x : M.H) : Prop := SmV (lieOf M.G) M.rep x

def repB (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : M.H →L[ℂ] M.H := M.rep (M.Q * m * M.Qi)

def IsLin (ℓ : M.H → M.Vp → ℂ) : Prop :=
  (∀ ξ, ∃ L : M.H →ₗ[ℂ] ℂ, SobC (lieOf M.G) M.rep L ∧ ∀ x, M.Sm x → ℓ x ξ = L x) ∧
    (∀ x, M.Sm x → IsLinearMap ℂ (ℓ x)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UWset k r M.z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ x, M.Sm x → ∀ ξ,
      ℓ (M.repB (h * m) x) (M.π h ξ) = psiGen k r M.z M.c m * ℓ x ξ

end Mod

def LinUniq : Prop :=
  ∀ (n k r : ℕ) (M : Mod n k r) (ℓ ℓ' : M.H → M.Vp → ℂ), M.IsLin ℓ → M.IsLin ℓ' →
    (∃ x, M.Sm x ∧ ∃ ξ, ℓ x ξ ≠ 0) → ∃ a : ℂ, ∀ x, M.Sm x → ∀ ξ, ℓ' x ξ = a * ℓ x ξ

def SepLin {n k r : ℕ} {ι : Type} [DecidableEq ι] (M : ι → Mod n k r)
    (la : (∀ i, (M i).H) → (∀ i, (M i).Vp) → ℂ) : Prop :=
  ∀ (i : ι) (x : ∀ j, (M j).H) (ξ : ∀ j, (M j).Vp), (∀ j, (M j).Sm (x j)) →
    (M i).IsLin fun y η => la (Function.update x i y) (Function.update ξ i η)

def LinMulti : Prop :=
  ∀ (n k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (M : ι → Mod n k r),
    (∀ la, SepLin M la → ∀ x ξ, (∀ j, (M j).Sm (x j)) → la x ξ = 0) ∨
    ∃ ℓ : ∀ i, (M i).H → (M i).Vp → ℂ, (∀ i, (M i).IsLin (ℓ i)) ∧ (∀ i, ∃ x, (M i).Sm x ∧ ∃ ξ, ℓ i x ξ ≠ 0) ∧
      ∀ la, SepLin M la → ∃ X : ℂ, ∀ x ξ, (∀ j, (M j).Sm (x j)) → la x ξ = X * ∏ i, ℓ i (x i) (ξ i)

end GlobalTheory.Ell
