import Mathlib

universe u

namespace GroundTheory.Arith.Modular

open Polynomial Polynomial.Bivariate

namespace Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

noncomputable def xC : W.toAffine.CoordinateRing := AdjoinRoot.mk W.toAffine.polynomial (C X)

noncomputable def yC : W.toAffine.CoordinateRing := AdjoinRoot.root W.toAffine.polynomial

theorem equation_xC_yC :
    yC W ^ 2 + algebraMap R _ W.a₁ * xC W * yC W + algebraMap R _ W.a₃ * yC W =
      xC W ^ 3 + algebraMap R _ W.a₂ * xC W ^ 2 + algebraMap R _ W.a₄ * xC W +
        algebraMap R _ W.a₆ := by
  have h : AdjoinRoot.mk W.toAffine.polynomial (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y -
      C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) = 0 := AdjoinRoot.mk_self
  have ha : ∀ a : R, algebraMap R W.toAffine.CoordinateRing a =
      AdjoinRoot.mk W.toAffine.polynomial (C (C a)) := fun a => rfl
  simp only [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_X] at h
  simp only [xC, yC, ha]
  linear_combination h

noncomputable def infPolynomial : R[X][Y] :=
  Y ^ 3 + C (C W.a₂ * X) * Y ^ 2 + C (C W.a₄ * X ^ 2 - C W.a₁ * X) * Y +
    C (C W.a₆ * X ^ 3 - C W.a₃ * X ^ 2 - X)

theorem natDegree_infPolynomial_lt : (C (C W.a₂ * X) * Y ^ 2 + C (C W.a₄ * X ^ 2 - C W.a₁ * X) * Y +
    C (C W.a₆ * X ^ 3 - C W.a₃ * X ^ 2 - X) : R[X][Y]).degree < 3 := by
  compute_degree!

theorem monic_infPolynomial : (infPolynomial W).Monic := by
  unfold infPolynomial
  rw [add_assoc, add_assoc]
  exact monic_X_pow_add (by simpa [add_assoc] using natDegree_infPolynomial_lt W)

abbrev InfChart : Type u := AdjoinRoot (infPolynomial W)

noncomputable def xI : InfChart W := AdjoinRoot.root (infPolynomial W)

noncomputable def zI : InfChart W := AdjoinRoot.of (infPolynomial W) X

theorem equation_xI_zI :
    xI W ^ 3 + algebraMap R _ W.a₂ * zI W * xI W ^ 2 +
      (algebraMap R _ W.a₄ * zI W ^ 2 - algebraMap R _ W.a₁ * zI W) * xI W +
        (algebraMap R _ W.a₆ * zI W ^ 3 - algebraMap R _ W.a₃ * zI W ^ 2 - zI W) = 0 := by
  have h : AdjoinRoot.mk (infPolynomial W) (Y ^ 3 + C (C W.a₂ * X) * Y ^ 2 +
      C (C W.a₄ * X ^ 2 - C W.a₁ * X) * Y + C (C W.a₆ * X ^ 3 - C W.a₃ * X ^ 2 - X)) = 0 :=
    AdjoinRoot.mk_self
  have ha : ∀ a : R, algebraMap R (InfChart W) a = AdjoinRoot.of (infPolynomial W) (C a) :=
    fun a => rfl
  simp only [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  simp only [xI, zI, ha]
  linear_combination h

abbrev Overlap : Type u := Localization.Away (yC W)

noncomputable def yInv : Overlap W := IsLocalization.Away.invSelf (yC W)

theorem yC_mul_yInv : algebraMap _ (Overlap W) (yC W) * yInv W = 1 :=
  IsLocalization.Away.mul_invSelf (yC W)

theorem eval₂_infPolynomial :
    (infPolynomial W).eval₂ (Polynomial.eval₂RingHom (algebraMap R (Overlap W)) (yInv W))
      (algebraMap _ (Overlap W) (xC W) * yInv W) = 0 := by
  have E := congrArg (algebraMap W.toAffine.CoordinateRing (Overlap W)) (equation_xC_yC W)
  have H := yC_mul_yInv W
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at E
  simp only [infPolynomial, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_sub,
    Polynomial.coe_eval₂RingHom]
  set u := yInv W
  set x := algebraMap _ (Overlap W) (xC W)
  set y := algebraMap _ (Overlap W) (yC W)
  linear_combination (-u ^ 3) * E +
    (algebraMap R (Overlap W) W.a₁ * x * u ^ 2 + algebraMap R (Overlap W) W.a₃ * u ^ 2 +
      u * (y * u + 1)) * H

noncomputable def infToOverlap : InfChart W →ₐ[R] Overlap W where
  toRingHom := AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap R (Overlap W)) (yInv W))
    (algebraMap _ (Overlap W) (xC W) * yInv W) (eval₂_infPolynomial W)
  commutes' a := by
    change AdjoinRoot.lift _ _ (eval₂_infPolynomial W) (AdjoinRoot.of _ (C a)) = _
    rw [AdjoinRoot.lift_of]
    simp

theorem infToOverlap_xI : infToOverlap W (xI W) = algebraMap _ (Overlap W) (xC W) * yInv W :=
  AdjoinRoot.lift_root (eval₂_infPolynomial W)

theorem infToOverlap_zI : infToOverlap W (zI W) = yInv W := by
  change AdjoinRoot.lift _ _ (eval₂_infPolynomial W) (AdjoinRoot.of _ X) = _
  rw [AdjoinRoot.lift_of]
  simp

end Weierstrass

end GroundTheory.Arith.Modular
