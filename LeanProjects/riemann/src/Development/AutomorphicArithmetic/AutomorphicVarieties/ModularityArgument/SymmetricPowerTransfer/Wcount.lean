import Mathlib

noncomputable section

namespace UpperTheory.V.Z.Sym

open MulAction

def gcount (H : Type) {Y : Type} [Group H] [MulAction H Y] (k : Y → ℂ) : ℂ :=
  ∑ᶠ o : orbitRel.Quotient H Y, k o.out / (Nat.card (stabilizer H o.out) : ℂ)

def wcount {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (k : Y → ℂ) : ℂ :=
  ∑ᶠ o : orbitRel.Quotient T Y, ((stabilizer T o.out).relIndex C : ℂ) * k o.out

def orb {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G) : ℂ :=
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  wcount C fun y : G ⧸ U => f (y.out⁻¹ * δ * θ y.out)

abbrev Etau (R : Type) [CommRing R] (τ : R) : Type := QuadraticAlgebra R (-1) τ

abbrev Lsq (R : Type) [CommRing R] (Δ : R) : Type := QuadraticAlgebra R Δ 0

example : gcount PUnit (fun _ : PUnit => (1 : ℂ)) = gcount PUnit (fun _ : PUnit => (1 : ℂ)) := rfl

end UpperTheory.V.Z.Sym
