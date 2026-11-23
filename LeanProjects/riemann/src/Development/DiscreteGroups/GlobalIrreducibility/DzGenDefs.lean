import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace DiscreteGroups.sglob.DzType

def eOne (m : ℕ) : (Σ _ : Fin m, Fin 1) ≃ Fin m := Equiv.sigmaUnique (Fin m) fun _ => Fin 1

def psOne (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) :=
  parInd (eOne m) (ofChar (1 : Levi k (fun _ : Fin m => Fin 1) →* ℂˣ))

def GenA : Prop :=
  GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ),
      (psOne k m).IsIrreducible ∧ IsSpherical (psOne k m) ∧ HasCentralChar (psOne k m) 1

def LatticeFiniteCohomologyGeneratorBound : Prop :=
  ∀ (K Γ : Type) [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (m : ℕ)
    (L U : Matrix (Fin m) (Fin m) K), (∀ i j, i < j → L i j = 0) → (∀ i, U i i = 1) → (∀ i j, j < i → U i j = 0) →
    (∀ i j, v ((L * U) i j) ≤ 1) → (∀ i, v ((L * U) i i) = 1) → (∀ i j, i < j → v ((L * U) i j) < 1) →
    ∀ i j, i < j → v (U i j) < 1

end DiscreteGroups.sglob.DzType
