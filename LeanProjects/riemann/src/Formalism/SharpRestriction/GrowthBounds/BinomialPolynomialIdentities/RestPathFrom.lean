import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.PathBasisTheorem
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.UnitAndFieldPowerLemmas
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.MemSpanImageIff

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def isV {N : ℕ} (LL : Letters (Fin N)) : ℕ → Bool := fun i => if h : i < N then LL.vec ⟨i, h⟩ else true

def Bn {N : ℕ} (B : Fin N → ℕ) : ℕ → ℕ := fun i => if h : i < N then B ⟨i, h⟩ else 0

def ext {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ℕ → Fin n → ℤ := fun i => if h : i < N + 1 then mu ⟨i, h⟩ else 0

def res (N : ℕ) {n : ℕ} (μ : ℕ → Fin n → ℤ) : Fin (N + 1) → Fin n → ℤ := fun i => μ i.val

def iv (N n : ℕ) : Fin N × Fin n → ℕ × Fin n := fun x => (x.1.val, x.2)

def RestPathTo : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) (ext P.mu) N

def RestPathFrom : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : ℕ → Fin n → ℤ),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) μ N → ∃ P : PPath n N LL B, P.mu = res N μ

def RestStd : Prop :=
  ∀ (n N : ℕ) (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)),
    IsSt mu I ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (pEnd mu) I

def RestPsi : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B)
    (I : ℤ → Finset (Fin n)), Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I →
    rename (iv N n) (Psi R P.mu I) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) (ext P.mu) N I

def RestPol : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (B : Fin N → ℕ),
    (Pol R n B).map (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB R n N (Bn B)

end Formalism.MainNotions.G.ColumnFamilies
