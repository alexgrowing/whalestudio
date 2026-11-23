import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ} {q : PrimeSpectrum R}

theorem PreChart.r_ne_zero (c : PreChart G N q) : c.r ≠ 0 := fun h => c.hr (h ▸ q.asIdeal.zero_mem)

def PreChart.toK (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (c : PreChart G N q) :
    Localization.Away c.r →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom (A := R) c.r (f := Algebra.ofId R K)
    (isUnit_iff_ne_zero.2 fun h => c.r_ne_zero (IsFractionRing.injective R K (h.trans (map_zero _).symm)))

theorem torsMap_mul {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (x y : Tors G N B) : torsMap φ (x * y) = torsMap φ x * torsMap φ y :=
  Subtype.ext (MonObj.comp_mul _ _ _)

theorem torsMap_one {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) :
    torsMap φ (1 : Tors G N B) = 1 :=
  Subtype.ext (MonObj.comp_one _)

theorem torsMap_comp {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (φ : B →ₐ[R] C) (ψ : C →ₐ[R] D) (z : Tors G N B) : torsMap ψ (torsMap φ z) = torsMap (ψ.comp φ) z :=
  Subtype.ext (by simp only [torsMap_val, ← Category.assoc, spOver_comp])

end GlobalTheory.GroupBplus.Aff
