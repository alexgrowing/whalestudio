import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Round

variable {O : Type} [CommRing O] (bar : O → O)

def IsMultCell (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ h : IsCell bar φ δ, LinearIndependent ℤ δ ∧ (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) ∧
    cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) = M

variable (O) in

structure FormFamily : Type 1 where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module O X]

  m : ℕ

  δ : Fin m → LinearMap.BilinForm ℤ X

attribute [instance] FormFamily.acg FormFamily.mod

variable {bar}

def FormFamily.Carries (c : FormFamily O) {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (e : X ≃ₗ[O] c.X) (s : Fin m ≃ Fin c.m), ∀ i, δ i = pull e.toLinearMap (c.δ (s i))

theorem FormFamily.carries_self (c : FormFamily O) : c.Carries c.δ :=
  ⟨LinearEquiv.refl O c.X, Equiv.refl _, fun _ => LinearMap.ext₂ fun _ _ => rfl⟩

variable (bar) in

def MultCellsAmong (q : ℕ) (φ : InvFun O) (M n : ℕ) : Prop :=
  ∃ R : Fin n → FormFamily O, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → ∃ k, (R k).Carries δ

def mulFormFamily : FormFamily ℤ := ⟨ℤ, 1, ![mulForm]⟩

example : mulFormFamily.Carries ![mulForm] := mulFormFamily.carries_self

theorem MultCellsAmong.succ {q : ℕ} {φ : InvFun O} {M n : ℕ} (h : MultCellsAmong bar q φ M n) :
    MultCellsAmong bar q φ M (n + 1) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨Fin.cons (FormFamily.mk PUnit 0 Fin.elim0) R, fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨k, hk⟩ := hR X hX m δ hδ
  exact ⟨k.succ, by simpa using hk⟩

end Round

end GlobalTheory.PolFan
