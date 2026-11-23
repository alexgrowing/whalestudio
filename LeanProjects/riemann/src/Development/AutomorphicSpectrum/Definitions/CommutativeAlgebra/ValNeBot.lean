import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def vl (la : HeightOneSpectrum (𝓞 K)) (x : K) : ℤ := -WithZero.log (la.valuation K x)

structure PtSys (K : Type) [Field K] [NumberField K] (R : Type) [CommRing R] [Algebra K R] where

  Pt : HeightOneSpectrum (𝓞 K) → Type

  val : ∀ {la}, Pt la → R → EReal
  val_zero : ∀ {la} (y : Pt la), val y 0 = ⊤
  val_ne_bot : ∀ {la} (y : Pt la) f, val y f ≠ ⊥
  val_add : ∀ {la} (y : Pt la) f g, min (val y f) (val y g) ≤ val y (f + g)
  val_smul : ∀ {la} (y : Pt la) (a : K) f, a ≠ 0 → val y (a • f) = (((vl la a : ℤ) : ℝ) : EReal) + val y f
  val_mul : ∀ {la} (y : Pt la) f g, val y (f * g) = val y f + val y g

namespace PtSys

variable {R : Type} [CommRing R] [Algebra K R] (S : PtSys K R)

def IsInt (f : R) : Prop := ∀ la (y : S.Pt la), 0 ≤ S.val y f

def lat (C : Submodule K R) : Set R := {f | f ∈ C ∧ S.IsInt f}

def BddDen (f : R) : Prop := ∃ N : 𝓞 K, N ≠ 0 ∧ S.IsInt ((N : K) • f)

def RefBound (C : Submodule K R) (la : HeightOneSpectrum (𝓞 K)) (e c : ℝ) (ph : S.Pt la → ℝ) : Prop :=
  ∀ y : S.Pt la, ∃ w ∈ S.lat C, S.val y w ≤ ((e + c * ph y : ℝ) : EReal)

def IsIdem {ι : Type} (comp : ∀ la, S.Pt la → ι) (u : ι → R) : Prop :=
  ∀ i la (y : S.Pt la), (comp la y = i → S.val y (u i) = 0) ∧ (comp la y ≠ i → S.val y (u i) = ⊤)

end PtSys

end

end GlobalTheory.CompanionTheory.Ar.Ref
