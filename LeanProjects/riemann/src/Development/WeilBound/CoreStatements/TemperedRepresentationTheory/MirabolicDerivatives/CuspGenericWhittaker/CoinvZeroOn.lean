import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
import GroundTheory.AutomorphicForms.LocallyConstantCompact
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.AutomorphicForms.WhittakerCells

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Matrix

namespace GlobalTheory.BZMir.Whit

abbrev lcc (X : Type) [TopologicalSpace X] : Submodule ℂ (X → ℂ) := GroundTheory.Automorphic.locallyConstantCompactSupport X ℂ ℂ

def twSpan {H X : Type} [Group H] [TopologicalSpace X] (act : H → X → X) (χ : H →* ℂˣ) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ (h : H) (f : X → ℂ), f ∈ lcc X ∧ g = (fun x => f (act h⁻¹ x)) - (χ h : ℂ) • f}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def biAct (n : ℕ) : unipB k (Fin n) × unipB k (Fin n) → GL (Fin n) k → GL (Fin n) k :=
  fun p x => (p.1 : GL (Fin n) k) * x * (p.2 : GL (Fin n) k)⁻¹

def biChar (ψ : AddChar k Circle) (n : ℕ) : unipB k (Fin n) × unipB k (Fin n) →* ℂˣ :=
  (whitChar ψ n).comp (MonoidHom.fst _ _) * ((whitChar ψ n).comp (MonoidHom.snd _ _))⁻¹

abbrev sigma {n : ℕ} (g : GL (Fin n) k) : GL (Fin n) k := GroundTheory.Automorphic.Whittaker.sigma g

variable (k) in

def biActOn (n : ℕ) (S : Set (GL (Fin n) k)) (hS : ∀ p, ∀ x ∈ S, biAct k n p x ∈ S) :
    unipB k (Fin n) × unipB k (Fin n) → S → S :=
  fun p x => ⟨biAct k n p x, hS p x x.2⟩

def CoinvZeroOn (ψ : AddChar k Circle) (n : ℕ) (S : Set (GL (Fin n) k)) : Prop :=
  ∀ hS : (∀ p, ∀ x ∈ S, biAct k n p x ∈ S), ∀ f ∈ lcc S, f ∈ twSpan (biActOn k n S hS) (biChar ψ n)

def SigmaTrivOn (ψ : AddChar k Circle) (n : ℕ) (S : Set (GL (Fin n) k)) : Prop :=
  ∀ (hS : ∀ p, ∀ x ∈ S, biAct k n p x ∈ S) (hσ : ∀ x ∈ S, sigma x ∈ S), ∀ f ∈ lcc S,
    (fun x : S => f ⟨sigma (x : GL (Fin n) k), hσ x x.2⟩) - f ∈ twSpan (biActOn k n S hS) (biChar ψ n)

def cell {n : ℕ} (w : Equiv.Perm (Fin n)) : Set (GL (Fin n) k) := {g | GroundTheory.Automorphic.Whittaker.bruhatCell g = w}

def IsRelevant {n : ℕ} (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1

end GlobalTheory.BZMir.Whit

end
