import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilOne

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.OneParam GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.RealK GlobalTheory.ThK.StepK

namespace GlobalTheory.ThK.StepK

def pOne (R S : ℕ) : Submodule ℂ (Mat (R + 1) (S + 1)) :=
  Submodule.span ℂ (nilOne R S ∪ Set.range embL ∪ {dC R S, dS R S})

section Mono

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def lowMono (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (l : List (Ix p q × Ix p q)) : Module.End ℂ V :=
  (l.map fun c => act (Eab c.2 c.1)).prod

def lowSpan (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (Λ : Ix p q → ℚ) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ l : List (Ix p q × Ix p q), (∀ c ∈ l, posC c.1 c.2) ∧ ∃ v ∈ hwSub act Λ, y = lowMono act l v}

def wtOf (μ : Ix p q → ℚ) (l : List (Ix p q × Ix p q)) : Ix p q → ℚ :=
  l.foldr (fun c ν => addRoot ν c.2 c.1) μ

@[simp] theorem wtOf_nil (μ : Ix p q → ℚ) : wtOf μ [] = μ := rfl

@[simp] theorem wtOf_cons (μ : Ix p q → ℚ) (c : Ix p q × Ix p q) (l : List (Ix p q × Ix p q)) :
    wtOf μ (c :: l) = addRoot (wtOf μ l) c.2 c.1 := rfl

@[simp] theorem lowMono_nil (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) : lowMono act [] v = v := rfl

@[simp] theorem lowMono_cons (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (c : Ix p q × Ix p q) (l : List (Ix p q × Ix p q)) (v : V) :
    lowMono act (c :: l) v = act (Eab c.2 c.1) (lowMono act l v) := by
  simp [lowMono]

end Mono

def shIx {R S : ℕ} : Ix R S → Ix (R + 1) (S + 1) := Sum.map Fin.succ Fin.succ

@[simp] theorem lowIx_shIx {R S : ℕ} (a : Ix R S) : lowIx (shIx a) = some a := by
  rcases a with a | a <;> rfl

@[simp] theorem lowIx_inl_zero {R S : ℕ} : lowIx (.inl 0 : Ix (R + 1) (S + 1)) = none := rfl

@[simp] theorem lowIx_inr_zero {R S : ℕ} : lowIx (.inr 0 : Ix (R + 1) (S + 1)) = none := rfl

def embLin (R S : ℕ) : Mat R S →ₗ[ℂ] Mat (R + 1) (S + 1) where
  toFun := embL
  map_add' X Y := by ext a b; simp only [embL, Matrix.of_apply, Matrix.add_apply]; split <;> simp
  map_smul' c X := by ext a b; simp only [embL, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split <;> simp

end GlobalTheory.ThK.StepK
