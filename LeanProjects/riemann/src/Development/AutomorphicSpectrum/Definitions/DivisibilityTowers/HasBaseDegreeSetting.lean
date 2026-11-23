import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

def hhFl (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (II : IntersectionSystem) : RP Ψ N →ₗ[ℝ] ℝ :=
  (basisMonomials (Ψ × Fin N) ℝ).constr ℝ fun m => (-1) ^ m.degree * hFlMono Ψ N II m

def HhTestBound {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (hh : RP Ψ N → ℝ) : Prop :=
  hh (testPoly j) ≤ ((dimX Ψ N j : ℝ) + 1) * testDeg Ψ N j *
    (Fintype.card Ψ * ((min j (N - j) : ℕ) / 2 * Real.log (N + 1)))

def RootTower.HasBaseDegreeSetting {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (II : IntersectionSystem) (Ch Cu rd Lval : ℝ) (B : ℕ) (c : T.Comp) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω)
    (E : Ψ → Type) (_ : ∀ τ, AddCommGroup (E τ)) (_ : ∀ τ, Module Ω (E τ)) (D : ComponentData II Ψ K ι Ω E)
    (O Lt : Type) (_ : CommRing O) (_ : AddCommGroup Lt) (_ : Module O Lt) (X : ComponentSetting D O Lt),
    D.N = N ∧ D.j = T.j ∧ X.rd = rd ∧ X.Lval = Lval ∧
    CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X ∧ 0 < degMu X.H ∧
    ArLimExists X.H X.S B ∧
    T.PPc II B c (testPoly T.j) = slX X B * (((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j))

end GlobalTheory.CompanionTheory.Ar.Top
