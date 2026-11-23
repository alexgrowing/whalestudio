import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Exists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

structure IsChain (j : K → FlBlock Ψ N) : Prop where
  inj : Function.Injective j
  down : ∀ k (q : FlBlock Ψ N), q.1 = (j k).1 → (q.2 : ℕ) ≤ (j k).2 → q ∈ Set.range j

abbrev PIdx (j : K → FlBlock Ψ N) : K → Type := fun k => FlIdx Ψ N (j k)

def yPart (j : K → FlBlock Ψ N) : (Σ k, PIdx j k) → ΩFl Ψ N := fun p => yFl Ψ N ⟨j p.1, p.2⟩

def PPart [Fintype K] (j : K → FlBlock Ψ N) : Ideal (MRing (PIdx j)) := mCoordIdeal (yPart j)

def unitLine [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k : K) : HermLine (PIdx j) :=
  fsHerm (PIdx j) fun k' => if k' = k then 1 else 0

def cellDim [Fintype K] (j : K → FlBlock Ψ N) : ℕ := ∑ k, (N - 1 - ((j k).2 : ℕ))

def dropJ (j : K → FlBlock Ψ N) (k₀ : K) : {k // k ≠ k₀} → FlBlock Ψ N := fun k => j k.1

def dropV (j : K → FlBlock Ψ N) (k₀ : K) : (Σ k, PIdx (dropJ j k₀) k) → Σ k, PIdx j k := fun p => ⟨p.1.1, p.2⟩

def constLine {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofWeight (fun _ => -1) fun _ _ _ => rfl

def rhoM (Ψ : Type) [Fintype Ψ] (N : ℕ) : (Ψ × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => N - 1 - (p.2 : ℕ)

def gapDelta (Ψ : Type) [Fintype Ψ] (N : ℕ) : MvPolynomial (Ψ × Fin N) ℝ :=
  ∏ τ : Ψ, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, ∑ s ∈ Finset.Ico a b, X (τ, s)

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
