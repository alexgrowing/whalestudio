import Formalism.FormalDegreeBessel.StatementDS

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

def dimLowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
    (((lowK ε lam + rhoC ε) a - (lowK ε lam + rhoC ε) b) / (rhoC ε a - rhoC ε b))

def cBetween {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℕ :=
  (univ.filter fun c : Fin n => a < c ∧ c < b ∧ ε c = ε a).card

def FdegFactorial : Prop :=
  ∀ n : ℕ, (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
    ∏ i ∈ range n, (i.factorial : ℝ)

def FdegDimV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    fdegHC lam = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)) /
      ∏ i ∈ range n, (i.factorial : ℝ)

def FdegVV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    fdegHC lam * (∏ i ∈ range n, (i.factorial : ℝ)) =
      ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)

def RhoCGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin n), a < b → ε a = ε b →
    rhoC ε a - rhoC ε b = 1 + (cBetween ε a b : ℝ)

def DimLowKPos : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → 0 < dimLowK ε lam

def DimLowKNat : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → ∃ d : ℕ, dimLowK ε lam = (d : ℝ)

def HolDimLowK : Prop :=
  ∀ (n : ℕ) (a b : ℝ), dimLowK (epsHol n) (lamHol n a b) = 1

end Formalism.QuantumDeterminants
