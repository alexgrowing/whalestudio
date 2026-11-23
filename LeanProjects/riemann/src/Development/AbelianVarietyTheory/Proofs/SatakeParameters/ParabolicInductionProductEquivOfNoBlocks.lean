import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmptyProd

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lineEquiv {α n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype n] [DecidableEq n]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) : IndSp e (piTensor σ) ≃ₗ[ℂ] ℂ :=
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  (LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)

theorem multiProd_equiv_of_isEmpty : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α']
    [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
    (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)),
    Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  intro k _ _ _ _ α α' n _ _ _ _ _ _ _ _ m _ _ m' _ _ e e' X _ _ X' _ _ σ σ'
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  refine ⟨Representation.Equiv.mk ((lineEquiv e σ).trans (lineEquiv e' σ').symm) fun g => ?_⟩
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

end GlobalTheory.EmptyProd
