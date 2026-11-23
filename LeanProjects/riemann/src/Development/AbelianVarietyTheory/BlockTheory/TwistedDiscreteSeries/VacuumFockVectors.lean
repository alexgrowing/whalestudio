import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain
open GlobalTheory.Ker (ipO)

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

def creOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') l g

def annOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  (-(fockScale D l.1 : ℂ)⁻¹) •
    annih (heisO ψ V W) θ l.1 (cplxO (cart M l.1) (cart M' l.1)) (unitMap (onb M l.1) (onb M' l.1) l.2.1 l.2.2) g

def multiFact {ι : Type} (α : ι →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

open Classical in

def FockLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : Prop :=
  (∀ P : PolF D W.rank V.rank, IsThetaFunO ψ V W (ptOf ψ θ M M' f P)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    creOp ψ θ M M' l (creOp ψ θ M M' l' g) = creOp ψ θ M M' l' (creOp ψ θ M M' l g)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    annOp ψ θ M M' l (creOp ψ θ M M' l' g) - creOp ψ θ M M' l' (annOp ψ θ M M' l g) = if l = l' then g else 0) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL W V) 𝓕 μ → ∀ α β : FVar D W.rank V.rank →₀ ℕ,
      ipO μ 𝓕 (ptOf ψ θ M M' f (MvPolynomial.monomial α 1)) (ptOf ψ θ M M' f (MvPolynomial.monomial β 1)) =
        if α = β then (multiFact α : ℂ) * ipO μ 𝓕 f f else 0) ∧
  Function.Injective (ptOf ψ θ M M' f)

def VacuumFock (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ f : WO V W → ℂ, IsVacVec ψ θ M M' f → FockLaws ψ θ M M' f

theorem ptOf_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : ptOf ψ θ M M' f 1 = f := by
  have h : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  unfold ptOf pureTensorO pureTensorL
  rw [h, Module.Basis.constr_basis]
  simp [opPow]

example : multiFact (Finsupp.single () 3) = 6 := by
  rw [multiFact, Finsupp.prod_single_index (by simp)]; rfl

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

end
