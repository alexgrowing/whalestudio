import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def sgn (e : Bool) : ℂ := if e then 1 else -1

def idx {n : ℕ} (ε : Fin n → Bool) : ℚ := ∑ a, if ε a then (1 : ℚ) else -1

def wtS {b : ℕ} (ε' : Fin b → Bool) (aT : ℚ) (e : Bool) : ℚ := (if e then -(idx ε' / 2) else idx ε' / 2) - aT

def wtT {a : ℕ} (ε : Fin a → Bool) (aS : ℚ) (e : Bool) : ℚ := (if e then idx ε / 2 else -(idx ε / 2)) + aS

def signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (g.submatrix (Subtype.val : {a // ε a = e} → Fin n) (Subtype.val : {a // ε a = e} → Fin n)).det

def elt {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

section Fock

variable {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def raiO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j))
    else -(MvPolynomial.pderiv (τ, i, j)).toLinearMap)

def lowO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (τ, i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j)))

def fockS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def fockT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (raiO τ ε ε' i j * lowO τ ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def subst (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) : PolF D b a →ₐ[ℂ] PolF D b a := by
  classical
  exact MvPolynomial.aeval fun v : FVar D b a =>
    if v.1 = τ then
      ∑ l, ∑ m, (if ε' v.2.1 = ε v.2.2 then k l v.2.1 * g m v.2.2 else star (k l v.2.1 * g m v.2.2)) •
        MvPolynomial.X (τ, l, m)
    else MvPolynomial.X v

end Fock

section Clauses

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
  (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
  (τ : D.what₂.Tau) (aS aT : ℚ)

def TorusVac : Prop :=
  ∀ (t : Fin V.rank → ℝ) (t' : Fin W.rank → ℝ),
    ω (elt θ M τ (diagonal fun j => Complex.exp (Complex.I * t j)),
        elt θ M' τ (diagonal fun i => Complex.exp (Complex.I * t' i))) f =
      Complex.exp (Complex.I * (∑ j, (wtS (M'.ε τ) aT (M.ε τ j) : ℂ) * t j +
        ∑ i, (wtT (M.ε τ) aS (M'.ε τ i) : ℂ) * t' i)) • f

def CompactFock : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (M.ε τ j) : ℚ) = wtS (M'.ε τ) aT (M.ε τ j)) ∧
    (∀ i, (y (M'.ε τ i) : ℚ) = wtT (M.ε τ) aS (M'.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f P) =
        (signBlockDeterminant (M.ε τ) true h ^ x true * signBlockDeterminant (M.ε τ) false h ^ x false *
          (signBlockDeterminant (M'.ε τ) true k ^ y true * signBlockDeterminant (M'.ε τ) false k ^ y false)) •
          ptOf ψ θ M M' f (subst τ (M.ε τ) (M'.ε τ) (h.map (starRingEnd ℂ)) k P)

def LieFock : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P -
        ((aT : ℂ) * X.trace) • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P +
        ((aS : ℂ) * Y.trace) • P) z) 0

end Clauses

def VacChar (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacVec ψ θ M M' f →
      TorusVac θ M M' ω f τ aS aT ∧ CompactFock ψ θ M M' ω f τ aS aT ∧ LieFock ψ θ M M' ω f τ aS aT

end GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

end
