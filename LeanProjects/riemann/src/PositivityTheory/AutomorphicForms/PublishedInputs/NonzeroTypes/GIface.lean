import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def HasDetVec {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V)
    (η : kˣ →* ℂˣ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ g ∈ KO k (Fin N), ρ g v = (η (GeneralLinearGroup.det g) : ℂ) • v

def IsTwSphProd {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    {s : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (η : Fin s → kˣ →* ℂˣ) : Prop :=
  ∃ (X : Fin s → Type) (_ : ∀ a, AddCommGroup (X a)) (_ : ∀ a, Module ℂ (X a))
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    (∀ a, IsSmooth (σ a)) ∧ (∀ a, (σ a).IsIrreducible) ∧ (∀ a, HasDetVec (σ a) (η a)) ∧
      Nonempty (π.Equiv (multiProd (stdBlocks d hd) σ))

end UpperTheory.TNZ
