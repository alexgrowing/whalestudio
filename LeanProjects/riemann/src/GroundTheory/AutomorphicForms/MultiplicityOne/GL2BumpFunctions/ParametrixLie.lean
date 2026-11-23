import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.GL2BumpFunctions.Parametrix
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Density
import GroundTheory.AutomorphicForms.DixmierMalliavinHaarCoord

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

def listOp : List 𝔤 → E → E
  | [], v => v
  | X :: L, v => h.derivOp π X (listOp L v)

@[simp] theorem listOp_nil (v : E) : h.listOp π [] v = v := rfl

theorem listOp_cons (X : 𝔤) (L : List 𝔤) (v : E) :
    h.listOp π (X :: L) v = h.derivOp π X (h.listOp π L v) := rfl

theorem listOp_append (L₁ L₂ : List 𝔤) (v : E) :
    h.listOp π (L₁ ++ L₂) v = h.listOp π L₁ (h.listOp π L₂ v) := by
  induction L₁ with
  | nil => rfl
  | cons X L ih => rw [List.cons_append, listOp_cons, listOp_cons, ih]

theorem isSmoothVector_listOp {v : E} (hv : h.IsSmoothVector π v) :
    ∀ L : List 𝔤, h.IsSmoothVector π (h.listOp π L v)
  | [] => hv
  | X :: L => h.isSmoothVector_derivOp π (isSmoothVector_listOp hv L) X

theorem listOp_eq_wordOp (L : List 𝔤) (v : E) :
    h.listOp π L v = h.wordOp π (fun i : Fin L.length => L[i]) v := by
  induction L with
  | nil => rfl
  | cons X L ih =>
    rw [listOp_cons, ih]
    show _ = h.wordOp π (k := L.length + 1) (fun i : Fin (L.length + 1) => (X :: L)[i]) v
    rw [wordOp_succ]
    rfl

variable [CompleteSpace E] (χ : ContDiffBump (0 : ℝ))

def parWord : {d : ℕ} → (Fin d → 𝔤) → (Fin d → Fin 3) → List 𝔤
  | 0, _, _ => []
  | _ + 1, b, α => parWord (Fin.tail b) (Fin.tail α) ++ List.replicate (α 0) (b 0)

def parKernel {d : ℕ} (α : Fin d → Fin 3) (t : Fin d → ℝ) : ℝ :=
  ∏ i, Parametrix.kernel χ (α i) (t i)

end IsExpLieAlgebra

end

end GroundTheory.Automorphic
