import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

namespace GlobalTheory.IndLineGL

open GlobalTheory.SmGL GlobalTheory.PRep
open scoped TensorProduct

variable (k : Type) [Field k]

def glCast {n m : ℕ} (h : n = m) : GL (Fin n) k →* GL (Fin m) k :=
  Units.map (Matrix.reindexAlgEquiv k k (finCongr h)).toMonoidHom

theorem glCast_rfl (n : ℕ) : glCast k (rfl : n = n) = MonoidHom.id _ := by
  ext g i j
  simp [glCast]

def midIncl (m : ℕ) : GL (Fin m) k →* Levi k (fun i : Fin 3 => Fin (blk3 m i)) :=
  MonoidHom.mulSingle (fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1

variable {k}

def colRep {α β : Type} [Fintype α] [Fintype β] [LinearOrder β] [DecidableEq β]
    {mr : α → Type} [∀ i, Fintype (mr i)] [∀ i, DecidableEq (mr i)]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    {W : Type} [AddCommGroup W] [Module ℂ W] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (f : ∀ i, (Σ j, c i j) ≃ mr i) (ρ : Representation ℂ (Levi k mr) W) (j : β) :
    Representation ℂ (Levi k fun i => c i j) (Jacquet ρ (relUnip k f)) :=
  ((relJac f ρ).comp (swapBlocks k c)).comp
    (MonoidHom.mulSingle (fun j => Levi k fun i => c i j) j)

end GlobalTheory.IndLineGL
