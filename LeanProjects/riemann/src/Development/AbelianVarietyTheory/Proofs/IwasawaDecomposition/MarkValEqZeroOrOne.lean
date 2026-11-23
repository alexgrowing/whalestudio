import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace Mark

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

def InFace (β x : LinearMap.BilinForm ℤ X) : Prop :=
  x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ (∀ y, β y y = 0 → x y y = 0) ∧
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x ∧ lab.evalZ (β + x) = lab.evalZ β

def IsIndec (β x : LinearMap.BilinForm ℤ X) : Prop :=
  InFace bar ψ lab β x ∧ x ≠ 0 ∧ ∀ y z, InFace bar ψ lab β y → InFace bar ψ lab β z → y ≠ 0 → z ≠ 0 → y + z ≠ x

variable (X) in

def IsMarked (β : LinearMap.BilinForm ℤ X) : Prop :=
  β ∈ balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    lab.evalZ β = ((i + 1 : ℕ) : ℝ) ∧
    ∃ S : Finset (LinearMap.BilinForm ℤ X), (∀ x, x ∈ S ↔ IsIndec bar ψ lab β x) ∧
      ∃ k : ℕ, 0 < k ∧ (k : ℤ) • β = ∑ x ∈ S, x

open Classical in

def markVal (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : ℝ :=
  if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b then
    (if IsMarked bar ψ lab i (Fin n → O) h.choose then 1 else 0) else 0

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

open Classical in

theorem markVal_int (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    markVal bar ψ lab i n (fun a b => (β a b : ℝ)) = if IsMarked bar ψ lab i (Fin n → O) β then 1 else 0 := by
  classical
  unfold markVal
  have h : ∃ β' : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, ((β a b : ℤ) : ℝ) = β' a b := ⟨β, fun _ _ => rfl⟩
  rw [dif_pos h]
  have e : h.choose = β := LinearMap.ext₂ fun a b => by
    have := h.choose_spec a b
    exact_mod_cast this.symm
  rw [e]

example : InFace (id : ℤ → ℤ) (zeroFun ℤ) (zeroFun ℤ) mulForm mulForm :=
  ⟨mem_balForms_int.2 fun y z => by simp [mul_comm], fun y => by simp [mul_self_nonneg], fun y h => h,
    by simp, by simp⟩

end Basic

end Mark

end GlobalTheory.PolFan
