import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA

noncomputable section

namespace PI.HwFix

open Formalism.BasicNotions Formalism.L2.DIV MvPolynomial
open scoped Matrix

section Stab

variable {n : ℕ} {ι : Type} [Fintype ι]

def MtwStable (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)) : Prop :=
  ∀ g : ι → GL (Fin n) ℂ, ∀ x ∈ S, rhoK lam g x ∈ S

def mtwHw (lam : ι → DomWeight n) : VV ℂ lam :=
  ⟨ten fun τ => extremal ℂ n (lam τ), Submodule.subset_span ⟨fun τ => extremal ℂ n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (PI.WGB.natW_anti_A (lam τ)), rfl⟩⟩

end Stab

def MtwUni {n : ℕ} {ι : Type} (g : ι → GL (Fin n) ℂ) : Prop :=
  ∀ τ, (∀ i j, j < i → ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    ∀ i, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1

def HwFixedEx : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (S : Submodule ℂ (VV ℂ lam)), S ≠ ⊥ → MtwStable lam S →
    ∃ v ∈ S, v ≠ 0 ∧ ∀ g : ι → GL (Fin n) ℂ, MtwUni g → rhoK lam g v = v

def HwFixedLine : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (v : VV ℂ lam),
    (∀ g : ι → GL (Fin n) ℂ, MtwUni g → rhoK lam g v = v) → ∃ c : ℂ, v = c • mtwHw lam

end PI.HwFix
