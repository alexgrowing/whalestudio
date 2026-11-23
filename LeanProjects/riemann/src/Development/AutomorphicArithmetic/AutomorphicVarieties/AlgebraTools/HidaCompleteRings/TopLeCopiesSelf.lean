import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Alg

variable {k G V N : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup N] [Module k N]

def Stab (ρ : Representation k G V) (W : Submodule k V) : Prop := ∀ g, ∀ v ∈ W, ρ g v ∈ W

structure IrrSub (ρ : Representation k G V) (W : Submodule k V) : Prop where
  stab : Stab ρ W
  ne : W ≠ ⊥
  irr : ∀ W' ≤ W, Stab ρ W' → W' = ⊥ ∨ W' = W

abbrev Into (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Type :=
  {f : N →ₗ[k] V // (∀ g v, f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y}

def copies (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Submodule k V :=
  ⨆ f : Into ρ Y σ, LinearMap.range f.1

theorem Stab.comp {ρ : Representation k G V} {W : Submodule k V} (h : Stab ρ W) {H : Type} [Group H] (j : H →* G) :
    Stab (ρ.comp j) W := fun x => h (j x)

def piRep (ρ : Representation k G V) (ι : Type) : Representation k G (ι → V) where
  toFun g := LinearMap.compLeft (ρ g) ι
  map_one' := by ext1 F; simp; rfl
  map_mul' a b := by ext1 F; simp; rfl

@[simp] theorem piRep_apply (ρ : Representation k G V) (ι : Type) (g : G) (F : ι → V) (i : ι) :
    piRep ρ ι g F i = ρ g (F i) := rfl

def IsTypeVec (σ : Representation k G N) (K : Subgroup G) {μ : Type} [Fintype μ] (τ : K → Matrix μ μ k) (e : μ → N) : Prop :=
  ∀ (x : K) a, ∑ b, τ x a b • σ x (e b) = e a

end Alg

structure LocFac {G H : Type} [Group G] [Group H] (j : H →* G) (p : G →* H) : Prop where
  left : ∀ h, p (j h) = h
  comm : ∀ g, p g = 1 → ∀ h, Commute (j h) g

theorem LocFac.dec {G H : Type} [Group G] [Group H] {j : H →* G} {p : G →* H} (h : LocFac j p) (g : G) :
    p ((j (p g))⁻¹ * g) = 1 := by rw [map_mul, map_inv, h.left, inv_mul_cancel]

structure PosForm {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  herm : ∀ u v, star (B u v) = B v u
  nonneg : ∀ v, 0 ≤ (B v v).re
  defn : ∀ v, B v v = 0 → v = 0
  inv : ∀ g u v, B (ρ g u) (ρ g v) = B u v

section Mass

variable {G : Type} [Group G]

def stabGrp (Γ K : Subgroup G) (x : G) : Subgroup G := Γ ⊓ K.map (MulAut.conj x).toMonoidHom

def massSum (Γ K : Subgroup G) (φ : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) K, φ q.out / (Nat.card (stabGrp Γ K q.out) : ℂ)

structure FinMass (Γ K : Subgroup G) : Prop where
  fin : Finite (DoubleCoset.Quotient (Γ : Set G) K)
  stab : ∀ x, Finite (stabGrp Γ K x)

end Mass

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
