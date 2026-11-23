import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory GlobalTheory.CompanionTheory.Ar.PB Filter Topology

variable {Ψ : Type} [Fintype Ψ] {N e : ℕ}

abbrev LowEnt (Ψ : Type) (N : ℕ) : Type := Ψ × {p : Fin N × Fin N // p.2 < p.1}

def lowMat (q : LowEnt Ψ N ≃ Fin e) (z : Fin e → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => if h : b < a then z (q ⟨τ, ⟨(a, b), h⟩⟩) else if a = b then 1 else 0

def cellDom (j : ℕ) (q : LowEnt Ψ N ≃ Fin e) : Set (Fin e → ℂ) := {z | ∀ τ, InFlagDomain N j (lowMat q z τ)}

def cellDens (j : ℕ) (q : LowEnt Ψ N ≃ Fin e) (z : Fin e → ℂ) : ℝ :=
  ∏ τ, ∏ i : Fin N, Real.exp (-4 * gramLog (sigForm N j) i (lowMat q z τ))

def cellVol (j : ℕ) (q : LowEnt Ψ N ≃ Fin e) (FF : Set (Fin e → ℂ)) : ENNReal :=
  ∫⁻ z in FF, ENNReal.ofReal (cellDens j q z)

structure PieceUnif (S : AnSys e (Ψ × Fin N)) (j n : ℕ) where

  q : Fin n → (LowEnt Ψ N ≃ Fin e)

  π : Fin n → (Fin e → ℂ) → S.X

  FF : Fin n → Set (Fin e → ℂ)
  mem_open : ∀ k, ∀ z ∈ cellDom j (q k), π k z ∈ S.open'
  param : ∀ k, ∀ z ∈ cellDom j (q k), ∃ V, z ∈ V ∧ V ⊆ cellDom j (q k) ∧ IsParam S.A V (π k)
  pot : ∀ k, ∀ z ∈ cellDom j (q k), ∀ p : Ψ × Fin N, ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G z ∧
    ∀ᶠ z' in 𝓝 z, (S.potH p).φ (π k z) (π k z') = stepPot N j p.2 (lowMat (q k) z' p.1) + (G z').re
  meas : ∀ k, MeasurableSet (FF k)
  sub : ∀ k, FF k ⊆ cellDom j (q k)
  inj : ∀ k, Set.InjOn (π k) (FF k)
  disj : Pairwise fun k k' => Disjoint (π k '' FF k) (π k' '' FF k')
  cover : IsNull S.A (⋃ k, π k '' FF k)ᶜ

def PieceUnif.vol {S : AnSys e (Ψ × Fin N)} {j n : ℕ} (U : PieceUnif S j n) (k : Fin n) : ENNReal :=
  cellVol j (U.q k) (U.FF k)

end GlobalTheory.CompanionTheory.Ar.Cmp
