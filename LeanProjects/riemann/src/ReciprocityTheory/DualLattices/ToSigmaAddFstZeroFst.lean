import ReciprocityTheory.DualLattices.ModuliPointsState

noncomputable section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

def tot (B : BX R₀) {R : LAlg R₀} {x y : B.G R} (u : B.P R x y) : Σ x y : B.G R, B.P R x y :=
  ⟨x, y, u⟩

def tmap (B : BX R₀) {R S : LAlg R₀} (f : LHom R S) (t : Σ x y : B.G R, B.P R x y) :
    Σ x y : B.G S, B.P S x y :=
  ⟨B.map f t.1, B.map f t.2.1, B.pmap f t.2.2⟩

variable {B : BX R₀} {R S T : LAlg R₀}

end BX

end ReciprocityTheory.PGsh
