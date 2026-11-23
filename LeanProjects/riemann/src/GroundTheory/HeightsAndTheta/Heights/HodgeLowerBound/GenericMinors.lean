import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerRatioTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

abbrev GenFrac (F : Type) [Field F] (Ψ : Type) (n : ℕ) : Type :=
  FractionRing (MvPolynomial (Ψ × Fin n × Fin n) F)

def genMatFr (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b =>
    algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) (X (τ, a, b))

def flagMinorRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : Ψ × Σ j : Fin (n - 1), PluckerBlocks n n j) :
    GenFrac F Ψ n :=
  flagMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2 / leadMinor (genMatFr F Ψ n q.1) q.2.1

abbrev PivotIdx (Ψ : Type) (n : ℕ) : Type := Ψ × Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) < b}

def pivotRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : PivotIdx Ψ n) : GenFrac F Ψ n :=
  pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / leadMinor (genMatFr F Ψ n q.1) q.2.1

theorem PlueckerData.ofΩ_eq {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type}
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)
    (x : Ω) : Pl.ofΩ x = algebraMap Ω (GenFrac Ω Ψ D.N) x := by
  rw [PlueckerData.ofΩ, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply Ω (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) (GenFrac Ω Ψ D.N)]

end GroundTheory.Heights₂.Heights.LowerBoundFree
