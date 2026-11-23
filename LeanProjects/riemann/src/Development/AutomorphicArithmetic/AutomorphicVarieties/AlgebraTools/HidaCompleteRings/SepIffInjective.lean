import Mathlib

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

variable {O R K : Type*} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K]

def Sep (Y : Set (R →ₐ[O] K)) : Prop := ∀ f : R, (∀ y ∈ Y, y f = 0) → f = 0

theorem Sep.mono {Y Y' : Set (R →ₐ[O] K)} (h : Sep Y) (hle : Y ⊆ Y') : Sep Y' :=
  fun f hf => h f fun y hy => hf y (hle hy)

theorem Sep.ext {Y : Set (R →ₐ[O] K)} (h : Sep Y) {a b : R} (hab : ∀ y ∈ Y, y a = y b) : a = b :=
  sub_eq_zero.1 (h _ fun y hy => by rw [map_sub, hab y hy, sub_self])

def kerPt [IsDomain K] (y : R →ₐ[O] K) : PrimeSpectrum R := ⟨RingHom.ker y, RingHom.ker_isPrime y⟩

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
