import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.PeriodIntegrals.AdelFinVol
import Formalism.PeriodIntegrals.AdelClassFin
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.PublishedAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FinCovolGA (D : D7) : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ (μ : Measure (GA D V)), μ.IsHaarMeasure → ∀ 𝓕 : Set (GA D V),
    IsFundamentalDomain (GQ V) 𝓕 μ → μ 𝓕 ≠ ⊤

def ClassFinGA (D : D7) : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
    ∃ S : Finset (GA D V), ∀ x : GA D V, ∃ γ ∈ GQ V, ∃ s ∈ S, ∃ r ∈ GinfC V, ∃ u ∈ U, x = γ * s * r * u

def StepFinCovolGA (D : D7) : Prop := PI.AdelFinVol.AdelFinVol → FinCovolGA D

def StepClassFinGA (D : D7) : Prop := PI.AdelClassFin.AdelClassFin → ClassFinGA D

def StepDSExists (D : D7) : Prop :=
  Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExists → ∀ (V : HSp D) (S : D.what₂.Tau → SPar),
    Formalism.IndefR.Mult.DSExists V S

def StrongApproxSU (D : D7) : Prop :=
  ∀ V : HSp D, 2 ≤ V.rank → ∀ e : AE D, IsSplitIdem D e → ∀ g : GA D V, (mt V g).det = 1 →
    g ∈ closure {x : GA D V | ∃ γ ∈ GQ V, (mt V γ).det = 1 ∧
      ∃ h : GA D V, (mt V h).det = 1 ∧ SuppAt e V h ∧ x = γ * h}

variable {D : D7}

def opPoly {X : Type} (A : (X → ℂ) → (X → ℂ)) (P : Polynomial ℂ) (φ : X → ℂ) : X → ℂ :=
  ∑ j ∈ P.support, P.coeff j • (A^[j] φ)

def AtTauExists (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∀ τ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) → ∃ x, IsAtTau θ V τ g x

theorem atTauExists_of {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (V : HSp D) :
    AtTauExists θ V := by
  intro τ g hg
  obtain ⟨x, hx, -⟩ := Formalism.IndefR.Eqv.atTauExUnique_holds (D := D) θ hθ V τ g hg
  exact ⟨x, hx⟩

def KtauS (V : HSp D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) :
    Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {k | k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ k * s τ = s τ * k}

def HCFiniteness (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (V : HSp D), AtTauExists θ V → ∀ (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ τ, Formalism.IndefR.Datum.IsCartanInv (gramAt D V τ) (s τ)) →
  ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
  ∀ (p : D.what₂.Tau → ℕ → Polynomial ℂ), (∀ τ j, p τ j ≠ 0) →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → Matrix ι ι ℂ),
    FiniteDimensional ℂ (Submodule.span ℂ {Φ : GA D V → (ι → ℂ) |
      (∀ i, IsAutFunSm θ V fun g => Φ g i) ∧
      (∀ τ, ∀ k ∈ KtauS V s τ, ∀ g, Φ (g * atTau θ V τ k) = (ρ τ k).mulVec (Φ g)) ∧
      (∀ u ∈ U, u ∈ GfC V → ∀ g, Φ (g * u) = Φ g) ∧
      ∀ τ, ∀ j < V.rank, ∀ i, opPoly (gelf θ V τ j) (p τ j) (fun g => Φ g i) = 0})

def KTypeSm {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) : Prop :=
  ∀ τ, ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W ∧
    ∀ w ∈ W, w ∈ M.sm τ

def GelfScalar (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∀ τ (j : ℕ), ∃ c : ℂ, ∀ T ∈ Formalism.IndefR.Mult.Mult θ M J χ, ∀ v : M.Vec, gelf θ V τ j (T v) = c • T v

def StepHCFinite (D : D7) : Prop :=
  HCFiniteness D → ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    KTypeSm M → GelfScalar θ M J χ →
    Formalism.IndefR.AutomorphicEvaluation.ResInjVec M (Formalism.IndefR.Mult.Mult θ M J χ) → Formalism.IndefR.Mult.HCFinite θ M J χ

end Formalism.IndefR.PublishedAut

end
