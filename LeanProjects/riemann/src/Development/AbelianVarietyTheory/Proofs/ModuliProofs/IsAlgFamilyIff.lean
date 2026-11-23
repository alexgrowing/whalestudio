import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CMUniformizationSpread
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMSpreadCompare

open GlobalTheory.PureType GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

def sgn (pos : Bool) : ℤˣ := if pos then 1 else -1

def typ (ε : ℤˣ) : Bool := decide (ε = 1)

theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := fun h => by
  have e := H.sqrt_neg_disc_sq
  rw [h, zero_pow two_ne_zero, zero_eq_neg, Nat.cast_eq_zero] at e
  exact H.d_prime.pos.ne' e

theorem map_rt (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
  have e : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  rw [H.sqrt_neg_disc_sq, ← map_pow, e, map_neg, map_natCast]

end Lattice

section Alg

variable {k R : Type} [CommRing k] [CommRing R] {X : Scheme.{0}} {a : k →+* R} {y : Sp R ⟶ X}
  {T : SAB H X} {t : SAB H (Sp R)} (m : SABMap t T y)

theorem exists_lift {A : Over (Sp k)} (φ : curveOver A a y ⟶ T.G) :
    ∃ φ' : (Over.pullback (spMap a)).obj A ⟶ t.G, φ'.left ≫ m.φ = φ.left :=
  ⟨Over.homMk (m.cart.1.lift φ.left (pullback.snd _ _) (Over.w φ)) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem exists_push {A : Over (Sp k)} (φ' : (Over.pullback (spMap a)).obj A ⟶ t.G) :
    ∃ φ : curveOver A a y ⟶ T.G, φ'.left ≫ m.φ = φ.left :=
  ⟨pushPt m.cart.1.w φ', rfl⟩

variable {A : Over (Sp k)} {φ : curveOver A a y ⟶ T.G} {φ' : (Over.pullback (spMap a)).obj A ⟶ t.G}

theorem exists_point {Z : Scheme.{0}} {s : Z ⟶ Sp R} (p : Over.mk (s ≫ spMap a) ⟶ A) :
    ∃ x : Over.mk s ⟶ (Over.pullback (spMap a)).obj A, p.left = x.left ≫ pullback.fst A.hom (spMap a) :=
  ⟨Over.homMk (pullback.lift p.left s (Over.w p)) (pullback.lift_snd _ _ _), (pullback.lift_fst _ _ _).symm⟩

end Alg

end GlobalTheory.CMSpreadCompare
