import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneSubOfIsIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion Matrix
open scoped TensorProduct

namespace GlobalTheory.InvTransposeEnds

section General

variable {G H V W Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_comp {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (φ : H →* G)
    (hφ : Function.Surjective φ) : Representation.IsIrreducible (ρ.comp φ) := by
  haveI hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := hφ g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases h.eq_bot_or_eq_top S' with e | e
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))

end General

section Matrices

variable {k : Type} [Field k]

theorem invTranspose_invTranspose (n : ℕ) (g : GL (Fin n) k) :
    invTranspose n k (invTranspose n k g) = g := by
  apply Units.ext
  show ((invTranspose n k g)⁻¹ : GL (Fin n) k).valᵀ = g.val
  rw [← map_inv]
  show ((g⁻¹)⁻¹ : GL (Fin n) k).valᵀᵀ = g.val
  rw [inv_inv, transpose_transpose]

def swapT (k : Type) [Field k] (a c : ℕ) : GL (Fin a) k × GL (Fin c) k ≃* GL (Fin c) k × GL (Fin a) k where
  toFun g := (invTranspose c k g.2, invTranspose a k g.1)
  invFun g := (invTranspose a k g.2, invTranspose c k g.1)
  left_inv g := Prod.ext (invTranspose_invTranspose _ _) (invTranspose_invTranspose _ _)
  right_inv g := Prod.ext (invTranspose_invTranspose _ _) (invTranspose_invTranspose _ _)
  map_mul' g g' := Prod.ext (map_mul (invTranspose c k) g.2 g'.2) (map_mul (invTranspose a k) g.1 g'.1)

section Blocks

variable {b N : ℕ} (h : b + 1 = N) (h' : 1 + b = N)

variable {h h'} {w : GL (Fin N) k}
  (hw : Placing.Moves (stdSum h) ((Equiv.sumComm _ _).trans (stdSum h')) w)
include hw

end Blocks

end Matrices

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

end Local

end GlobalTheory.InvTransposeEnds
