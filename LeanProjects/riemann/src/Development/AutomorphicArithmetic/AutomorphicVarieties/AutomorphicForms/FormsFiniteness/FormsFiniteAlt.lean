import GroundTheory.AutomorphicForms.AutomorphicFormSpaces

noncomputable section

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Af.Fin

def AlgMod {M : Type} [AddCommGroup M] [Module ℂ M] (S N : Submodule ℂ M) (T : Module.End ℂ M) : Prop :=
  ∃ p : Polynomial ℂ, p.Monic ∧ ∀ x ∈ S, Polynomial.aeval T p x ∈ N

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def Growth (S : Submodule ℂ (archSmooth K n)) : Prop := ∀ φ ∈ S, HasModerateGrowth φ.1

def Level (S : Submodule ℂ (archSmooth K n)) : Prop :=
  ∃ L : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (L : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
    ∀ φ ∈ S, ∀ u ∈ L, ∀ g, φ.1 (g * finEmb K n u) = φ.1 g

def Types (S : Submodule ℂ (archSmooth K n)) : Prop :=
  ∃ V : Submodule ℂ (archCompact K n → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
    ∀ φ ∈ S, ∀ g, (fun k : archCompact K n => φ.1 (g * infEmb K n k.1)) ∈ V

def Centre (S : Submodule ℂ (archSmooth K n)) : Prop :=
  ∀ z ∈ (isExpLieAlgebra K n).centerU, AlgMod S ⊥ (uAction z)

structure Bdd (S : Submodule ℂ (archSmooth K n)) : Prop where
  left : ∀ φ ∈ S, IsLeftInvariant φ.1
  growth : Growth S
  level : Level S
  types : Types S
  centre : Centre S

theorem AlgMod.mono {M : Type} [AddCommGroup M] [Module ℂ M] {S S' N : Submodule ℂ M} {T : Module.End ℂ M}
    (h : AlgMod S N T) (hS : S' ≤ S) : AlgMod S' N T := by
  obtain ⟨p, hp, hx⟩ := h
  exact ⟨p, hp, fun x hxS => hx x (hS hxS)⟩

theorem Bdd.mono {S S' : Submodule ℂ (archSmooth K n)} (h : Bdd S) (hS : S' ≤ S) : Bdd S' where
  left φ hφ := h.left φ (hS hφ)
  growth φ hφ := h.growth φ (hS hφ)
  level := h.level.imp fun _ hL => ⟨hL.1, fun φ hφ => hL.2 φ (hS hφ)⟩
  types := h.types.imp fun _ hV => ⟨hV.1, hV.2.1, fun φ hφ => hV.2.2 φ (hS hφ)⟩
  centre z hz := (h.centre z hz).mono hS

variable (K n) in

def FinAt : Prop := ∀ S : Submodule ℂ (archSmooth K n), Bdd S → FiniteDimensional ℂ S

def FormsFinite : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), FinAt K n

end UpperTheory.V.Af.Fin
