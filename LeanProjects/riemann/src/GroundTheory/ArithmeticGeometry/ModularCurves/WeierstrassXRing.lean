import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCharts

universe u

namespace GroundTheory.Arith.Modular

open Polynomial Polynomial.Bivariate

namespace Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

noncomputable def xPolynomial : R[X][Y] :=
  Y ^ 3 + C (C W.a₂) * Y ^ 2 + C (C W.a₄ - C W.a₁ * X) * Y + C (C W.a₆ - X ^ 2 - C W.a₃ * X)

theorem degree_xPolynomial_lt : (C (C W.a₂) * Y ^ 2 + C (C W.a₄ - C W.a₁ * X) * Y +
    C (C W.a₆ - X ^ 2 - C W.a₃ * X) : R[X][Y]).degree < 3 := by
  compute_degree!

theorem monic_xPolynomial : (xPolynomial W).Monic := by
  unfold xPolynomial
  rw [add_assoc, add_assoc]
  exact monic_X_pow_add (by simpa [add_assoc] using degree_xPolynomial_lt W)

theorem natDegree_xPolynomial [Nontrivial R] : (xPolynomial W).natDegree = 3 := by
  unfold xPolynomial
  compute_degree!

abbrev XRing : Type u := AdjoinRoot (xPolynomial W)

theorem eval₂_polynomial_XRing :
    (W.toAffine.polynomial).eval₂ (Polynomial.eval₂RingHom (algebraMap R (XRing W))
      (AdjoinRoot.root (xPolynomial W))) (AdjoinRoot.of (xPolynomial W) X) = 0 := by
  have h : AdjoinRoot.mk (xPolynomial W) (Y ^ 3 + C (C W.a₂) * Y ^ 2 + C (C W.a₄ - C W.a₁ * X) * Y +
      C (C W.a₆ - X ^ 2 - C W.a₃ * X)) = 0 := AdjoinRoot.mk_self
  simp only [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, coe_eval₂RingHom]
  have ha : ∀ a : R, algebraMap R (XRing W) a = AdjoinRoot.of (xPolynomial W) (C a) := fun a => rfl
  simp only [ha]
  linear_combination -h

theorem eval₂_xPolynomial_coord :
    (xPolynomial W).eval₂ (Polynomial.eval₂RingHom (algebraMap R W.toAffine.CoordinateRing) (yC W))
      (xC W) = 0 := by
  have E := equation_xC_yC W
  simp only [xPolynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom]
  linear_combination -E

noncomputable def toXRing : W.toAffine.CoordinateRing →+* XRing W :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap R (XRing W)) (AdjoinRoot.root (xPolynomial W)))
    (AdjoinRoot.of (xPolynomial W) X) (eval₂_polynomial_XRing W)

noncomputable def ofXRing : XRing W →+* W.toAffine.CoordinateRing :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap R W.toAffine.CoordinateRing) (yC W))
    (xC W) (eval₂_xPolynomial_coord W)

theorem infNatDegree [Nontrivial R] : (infPolynomial W).natDegree = 3 := by
  unfold infPolynomial
  compute_degree!

theorem ofXRing_toXRing (a : W.toAffine.CoordinateRing) : ofXRing W (toXRing W a) = a := by
  change ((ofXRing W).comp (toXRing W)) a = RingHom.id _ a
  congr 1
  apply AdjoinRoot.ringHom_ext
  · ext p
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_C, RingHom.id_apply]
      change AdjoinRoot.lift _ _ (eval₂_xPolynomial_coord W) (AdjoinRoot.of _ (C p)) = _
      rw [AdjoinRoot.lift_of]
      simp
      rfl
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_X, RingHom.id_apply, AdjoinRoot.lift_root]
      rfl
  · simp [toXRing, ofXRing, yC]

theorem toXRing_ofXRing (a : XRing W) : toXRing W (ofXRing W a) = a := by
  change ((toXRing W).comp (ofXRing W)) a = RingHom.id _ a
  congr 1
  apply AdjoinRoot.ringHom_ext
  · ext p
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_C, RingHom.id_apply]
      change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.of _ (C p)) = _
      rw [AdjoinRoot.lift_of]
      simp
      rfl
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_X, RingHom.id_apply, yC, AdjoinRoot.lift_root]
  · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_root, RingHom.id_apply, xC,
      AdjoinRoot.mk_C, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

noncomputable def xRingEquiv : W.toAffine.CoordinateRing ≃+* XRing W :=
  RingEquiv.ofRingHom (toXRing W) (ofXRing W) (RingHom.ext (toXRing_ofXRing W))
    (RingHom.ext (ofXRing_toXRing W))

noncomputable def xAlgEquiv : W.toAffine.CoordinateRing ≃ₐ[R] XRing W :=
  AlgEquiv.ofRingEquiv (f := xRingEquiv W) (fun r => by
    change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.of _ (C r)) = _
    rw [AdjoinRoot.lift_of]
    simp)

theorem xAlgEquiv_xC : xAlgEquiv W (xC W) = AdjoinRoot.root (xPolynomial W) := by
  change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.mk _ (C X)) = _
  rw [AdjoinRoot.mk_C, AdjoinRoot.lift_of]
  simp

theorem xAlgEquiv_yC : xAlgEquiv W (yC W) = AdjoinRoot.of (xPolynomial W) X := by
  change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.root _) = _
  rw [AdjoinRoot.lift_root]

section Bases

variable [Nontrivial R]

noncomputable def basisX : Module.Basis (Fin 3) R[X] (XRing W) :=
  (AdjoinRoot.powerBasis' (monic_xPolynomial W)).basis.reindex (finCongr (natDegree_xPolynomial W))

theorem basisX_apply (i : Fin 3) : basisX W i = AdjoinRoot.root (xPolynomial W) ^ (i : ℕ) := by
  rw [basisX, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

noncomputable def basisI : Module.Basis (Fin 3) R[X] (InfChart W) :=
  (AdjoinRoot.powerBasis' (monic_infPolynomial W)).basis.reindex (finCongr (infNatDegree W))

theorem basisI_apply (i : Fin 3) : basisI W i = xI W ^ (i : ℕ) := by
  rw [basisI, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

end Bases

end Weierstrass

end GroundTheory.Arith.Modular
