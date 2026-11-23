import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

noncomputable section

open scoped Classical Pointwise

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Carry

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T' : E}

structure c3eqv_Carry (Λ : Submodule (𝓞 E) S.V) (φ : S.V ≃ₗ[E] S.V) (F₁ F₂ : LFlag S r T') : Prop where
  iso : φ ∈ Formalism.HermitianLatticesTheory.isom S.hT
  lam : ∀ y ∈ Λ, φ y ∈ Λ
  lam' : ∀ y ∈ Λ, φ.symm y ∈ Λ
  X : ∀ x ∈ Xsp F₁, φ x ∈ Xsp F₂
  X' : ∀ x ∈ Xsp F₂, φ.symm x ∈ Xsp F₁
  z : φ F₁.fl.z - F₂.fl.z ∈ Xsp F₂

variable {Λ : Submodule (𝓞 E) S.V} {φ ψ : S.V ≃ₗ[E] S.V} {F₁ F₂ F₃ : LFlag S r T'}

theorem c3eqv_Carry.symm (h : c3eqv_Carry Λ φ F₁ F₂) : c3eqv_Carry Λ φ.symm F₂ F₁ where
  iso := c3eqv_isom_symm h.iso
  lam := h.lam'
  lam' := by simpa using h.lam
  X := h.X'
  X' := by simpa using h.X
  z := by
    have h1 := h.X' _ h.z
    have : φ.symm F₂.fl.z - F₁.fl.z = -(φ.symm (φ F₁.fl.z - F₂.fl.z)) := by simp
    rw [this]
    exact Submodule.neg_mem _ h1

theorem c3eqv_Carry.trans (h : c3eqv_Carry Λ φ F₁ F₂) (h' : c3eqv_Carry Λ ψ F₂ F₃) :
    c3eqv_Carry Λ (φ.trans ψ) F₁ F₃ where
  iso := c3eqv_isom_trans h.iso h'.iso
  lam := fun y hy => h'.lam _ (h.lam y hy)
  lam' := fun y hy => h.lam' _ (h'.lam' y hy)
  X := fun x hx => h'.X _ (h.X x hx)
  X' := fun x hx => h.X' _ (h'.X' x hx)
  z := by
    have h1 := h'.X _ h.z
    have : (φ.trans ψ) F₁.fl.z - F₃.fl.z = ψ (φ F₁.fl.z - F₂.fl.z) + (ψ F₂.fl.z - F₃.fl.z) := by simp
    rw [this]
    exact Submodule.add_mem _ h1 h'.z

variable {T : E} {F : LFlag S r T}

end Carry

section D7

variable (D : D7)

end D7

section Main

variable (D : D7)

end Main

section Step4

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def TermFlagLatticesCongruent (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' →
    (∀ x' ∈ Lrep Λ F', ∃ l ∈ Lrep Λ (lf D F0), l - x' ∈ NgX Λ (gS D) (lf D F0) F') ∧
    XLam Λ (lf D F0) ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F'

end Step4

end Formalism.MainNotions.BridgeLemma₂

end
