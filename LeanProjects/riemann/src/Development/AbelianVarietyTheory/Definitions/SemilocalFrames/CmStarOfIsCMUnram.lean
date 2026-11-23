import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

namespace GlobalTheory.SA

open NumberField Module Formalism.BasicNotions

def CMStar (E : Type) [Field E] [StarRing E] : Prop :=
  ∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)

section AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def NDLat (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : Prop :=
  M.FG ∧ ∀ x ∈ Submodule.span E (M : Set V), (∀ y ∈ M, h y x = 0) → x = 0

def PosOn (h : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V) : Prop :=
  ∀ τ : E →+* ℂ, ∀ x ∈ U, x ≠ 0 → 0 < (τ (h x x)).re

def projAway (h : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V) (M : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {s | (∀ u ∈ U, h u s = 0) ∧ ∃ x ∈ M, x - s ∈ U}

omit [NumberField E] [StarRing E] in

theorem int_smul_eq (c : 𝓞 E) (x : V) : c • x = (c : E) • x :=
  (IsScalarTower.algebraMap_smul E c x).symm

omit [NumberField E] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] in

theorem PosOn.mono {h : V →ₗ⋆[E] V →ₗ[E] E} {U U' : Submodule E V} (hU : PosOn h U) (hle : U' ≤ U) :
    PosOn h U' := fun τ x hx => hU τ x (hle hx)

omit [NumberField E] [IsScalarTower (𝓞 E) E V] in

theorem orth_span (h : V →ₗ⋆[E] V →ₗ[E] E) {M : Submodule (𝓞 E) V} {x : V} (hx : ∀ y ∈ M, h y x = 0) :
    ∀ y ∈ Submodule.span E (M : Set V), h y x = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hx y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]

omit [NumberField E] in

theorem ndLat_of_isLattice {h : V →ₗ⋆[E] V →ₗ[E] E} (hn : h.Nondegenerate) {M : Submodule (𝓞 E) V}
    (hM : Submodule.IsLattice E M) : NDLat h M :=
  ⟨hM.fg, fun x _ h0 => hn.2 x fun y => orth_span h h0 y (by rw [hM.span_eq_top]; trivial)⟩

end AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

structure Amb (S : HSpace E) (k r : ℕ) : Prop where
  cm : CMStar E
  dim : finrank E S.V = k + 2 * r + 1
  neg : ∀ (τ : E →+* ℂ) (U : Submodule E S.V), (∀ x ∈ U, (τ (S.hT x x)).re ≤ 0) → finrank E U ≤ r + 1

abbrev gL {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) : Submodule (𝓞 E) S.V :=
  Ideal.span {(g : 𝓞 E)} • Λ

theorem mem_gL {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (x : S.V) :
    x ∈ gL Λ g ↔ ∃ y ∈ Λ, (g : E) • y = x := by
  rw [gL, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [int_smul_eq]
  rfl

section Diagonal

open Formalism.BasicNotions.Examples₂

def wittSigns (k r : ℕ) : Fin (k + 2 * r + 1) → Bool := fun i => decide ((i : ℕ) < r + 1)

def wittSpace (E : Type) [Field E] [NumberField E] [StarRing E] (k r : ℕ) : HSpace E :=
  stdSpace star_isIntegral (k + 2 * r + 1) (wittSigns k r) (k + r) (r + 1)

example (k r : ℕ) : NDLat (wittSpace E k r).hT (wittSpace E k r).L0 :=
  ndLat_of_isLattice (wittSpace E k r).nondeg (wittSpace E k r).standardTuple_isLattice

end Diagonal

end GlobalTheory.SA

end
