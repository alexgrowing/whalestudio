import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PowFamIsDeligneMeas

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.UnitFiltration

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_close {θ : kˣ →* ℂˣ} {m : ℕ} (hθ : ∀ x ∈ unitFilt k m, θ x = 1) {u s : kˣ}
    (hus : valuation k (u : k) = valuation k (s : k))
    (h : valuation k ((u : k) - s) ≤ uniformizer k ^ m * valuation k (s : k)) : θ u = θ s := by
  have hs0 : 0 < valuation k (s : k) := by simp [zero_lt_iff]
  have hmem : u * s⁻¹ ∈ unitFilt k m := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hus, mul_inv_cancel₀ hs0.ne']
    · have e : ((u * s⁻¹ : kˣ) : k) - 1 = ((u : k) - s) * (s : k)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ s.ne_zero]
      rw [e, map_mul, map_inv₀, mul_inv_le_iff₀ hs0]
      exact h
  have := hθ _ hmem
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

def ballSub (p : kˣ) : AddSubgroup k where
  carrier := cball p
  add_mem' := add_mem_cball
  zero_mem' := by simp [cball]
  neg_mem' := neg_mem_cball

theorem mem_ballSub {p : kˣ} {z : k} : z ∈ ballSub p ↔ valuation k z ≤ valuation k (p : k) := Iff.rfl

theorem val_one_add {p : kˣ} (hp : valuation k (p : k) < 1) (z : ballSub p) : valuation k (1 + (z : k)) = 1 :=
  Valuation.map_one_add_of_lt _ (lt_of_le_of_lt (mem_ballSub.1 z.2) hp)

def onePlus {p : kˣ} (hp : valuation k (p : k) < 1) (z : ballSub p) : kˣ :=
  Units.mk0 (1 + (z : k)) (fun h0 => by
    have := val_one_add hp z
    rw [h0, map_zero] at this
    exact zero_ne_one this)

@[simp] theorem val_onePlus {p : kˣ} (hp : valuation k (p : k) < 1) (z : ballSub p) :
    ((onePlus hp z : kˣ) : k) = 1 + (z : k) := rfl

def addCharOn (ψ : AddChar k Circle) (p : kˣ) (w : k) : Multiplicative (ballSub p) →* ℂ where
  toFun z := (ψ (w * ((Multiplicative.toAdd z : ballSub p) : k)) : ℂ)
  map_one' := by simp
  map_mul' x y := by simp [mul_add, AddChar.map_add_eq_mul]

@[simp] theorem addCharOn_apply (ψ : AddChar k Circle) (p : kˣ) (w : k) (z : Multiplicative (ballSub p)) :
    addCharOn ψ p w z = (ψ (w * ((Multiplicative.toAdd z : ballSub p) : k)) : ℂ) := rfl

def alphaChar (α : kˣ →* ℂˣ) {p : kˣ} (hp : valuation k (p : k) < 1) {m : ℕ} (hα : ∀ x ∈ unitFilt k m, α x = 1)
    (hpm : valuation k (p : k) * valuation k (p : k) ≤ uniformizer k ^ m) : Multiplicative (ballSub p) →* ℂ where
  toFun z := (α (onePlus hp (Multiplicative.toAdd z)) : ℂ)
  map_one' := by
    have : onePlus hp (Multiplicative.toAdd (1 : Multiplicative (ballSub p))) = 1 := Units.ext (by simp)
    rw [this, map_one, Units.val_one]
  map_mul' x y := by
    rw [← Units.val_mul, ← map_mul]
    congr 1
    refine (eq_of_close hα ?_ ?_).symm
    · rw [Units.val_mul, map_mul, val_onePlus, val_onePlus, val_onePlus, val_one_add hp, val_one_add hp, mul_one]
      have := val_one_add hp (Multiplicative.toAdd (x * y))
      simpa using this.symm
    · have e : ((onePlus hp (Multiplicative.toAdd x) * onePlus hp (Multiplicative.toAdd y) : kˣ) : k) -
          ((onePlus hp (Multiplicative.toAdd (x * y)) : kˣ) : k) =
          ((Multiplicative.toAdd x : ballSub p) : k) * ((Multiplicative.toAdd y : ballSub p) : k) := by
        simp only [Units.val_mul, val_onePlus, toAdd_mul, AddSubgroup.coe_add]
        ring
      have h1 := val_one_add hp (Multiplicative.toAdd (x * y))
      rw [e, map_mul, val_onePlus, h1, mul_one]
      exact (mul_le_mul' (mem_ballSub.1 (Multiplicative.toAdd x).2) (mem_ballSub.1 (Multiplicative.toAdd y).2)).trans hpm

@[simp] theorem alphaChar_apply (α : kˣ →* ℂˣ) {p : kˣ} (hp : valuation k (p : k) < 1) {m : ℕ}
    (hα : ∀ x ∈ unitFilt k m, α x = 1) (hpm : valuation k (p : k) * valuation k (p : k) ≤ uniformizer k ^ m)
    (z : Multiplicative (ballSub p)) :
    alphaChar α hp hα hpm z = (α (onePlus hp (Multiplicative.toAdd z)) : ℂ) := rfl

end Local

section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {c : kˣ} {m : ℕ} {R : Finset kˣ} {θ : kˣ →* ℂˣ}

end Sums

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

end PositivityTheory.Pf1.LocalLanglands.UnitFiltration

end
