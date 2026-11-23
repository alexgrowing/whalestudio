import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassProj

open CategoryTheory AlgebraicGeometry

universe u

namespace GroundTheory.Arith.Modular

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section General

variable {j : Fin 3} {T : Type u} [CommRing T] (ψ : MvPolynomial (Fin 3) R →+* T)
  (hψ1 : ψ (X j) = 1) (hψF : ψ W.toProjective.polynomial = 0)

noncomputable def liftHom : HomRing W →+* T :=
  Ideal.Quotient.lift (cubicIdeal W) ψ (fun a ha => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hψF, mul_zero])

include hψ1 in
theorem liftHom_var : liftHom W ψ hψF (var W j) = 1 := hψ1

noncomputable def awayTo : Away (homGrading W) (var W j) →+* T :=
  (Localization.awayLift (liftHom W ψ hψF) (var W j)
    (by rw [liftHom_var W ψ hψ1 hψF]; exact isUnit_one)).comp
    (algebraMap (Away (homGrading W) (var W j)) (Localization.Away (var W j)))

theorem awayTo_mk (m : ℕ) (P : MvPolynomial (Fin 3) R) (hP : π W P ∈ homGrading W (m • 1)) :
    awayTo W ψ hψ1 hψF (Away.mk (homGrading W) (var_mem W j) m (π W P) hP) = ψ P := by
  have := Localization.awayLift_mk (liftHom W ψ hψF) (var W j) (π W P) 1
    (by rw [liftHom_var W ψ hψ1 hψF, one_mul]) m
  simp only [awayTo, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  refine this.trans ?_
  rw [one_pow, mul_one]
  rfl

theorem awayTo_surjective (hsurj : Function.Surjective ψ) :
    Function.Surjective (awayTo W ψ hψ1 hψF) := by
  intro t
  obtain ⟨P, rfl⟩ := hsurj t
  refine ⟨∑ m ∈ Finset.range (P.totalDegree + 1),
    Away.mk (homGrading W) (var_mem W j) m (π W (homogeneousComponent m P))
      (mk_mem_quotGrading _ _ (by simpa using homogeneousComponent_mem m P)), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← sum_homogeneousComponent P]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => awayTo_mk W ψ hψ1 hψF m _ _

theorem val_eq_scale (m : ℕ) (P : MvPolynomial (Fin 3) R) (hP : P.IsHomogeneous m)
    (hP' : π W P ∈ homGrading W (m • 1)) :
    (Away.mk (homGrading W) (var_mem W j) m (π W P) hP').val = scale (π W) j P := by
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  exact (scale_homog (π W) j hP).symm

noncomputable def awayEquiv (hsurj : Function.Surjective ψ)
    (θ : T →+* Away (homGrading W) (var W j))
    (hθ : ∀ P, (θ (ψ P)).val = scale (π W) j P) : Away (homGrading W) (var W j) ≃+* T :=
  RingEquiv.ofBijective (awayTo W ψ hψ1 hψF) ⟨by
    have hleft : ∀ z, θ (awayTo W ψ hψ1 hψF z) = z := by
      intro z
      obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective (homGrading W) (var_mem W j) z
      obtain ⟨P, hP, rfl⟩ := ha
      have hP1 : P.IsHomogeneous m := (mem_homogeneousSubmodule _ P).1 (by simpa using hP)
      refine (congrArg θ (awayTo_mk W ψ hψ1 hψF m P (mk_mem_quotGrading _ _ hP))).trans ?_
      apply HomogeneousLocalization.val_injective
      rw [hθ]
      exact (val_eq_scale W m P hP1 (mk_mem_quotGrading _ _ hP)).symm
    exact Function.LeftInverse.injective hleft, awayTo_surjective W ψ hψ1 hψF hsurj⟩

theorem awayEquiv_apply (hsurj : Function.Surjective ψ)
    (θ : T →+* Away (homGrading W) (var W j))
    (hθ : ∀ P, (θ (ψ P)).val = scale (π W) j P) (z : Away (homGrading W) (var W j)) :
    awayEquiv W ψ hψ1 hψF hsurj θ hθ z = awayTo W ψ hψ1 hψF z := rfl

end General

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem π_C (a : R) : π W (C a) = algebraMap R (HomRing W) a := rfl

section ChartZ

noncomputable def dehomZ : MvPolynomial (Fin 3) R →+* W.toAffine.CoordinateRing :=
  eval₂Hom (algebraMap R _) ![xC W, yC W, 1]

theorem dehomZ_X_two : dehomZ W (X 2) = 1 := by simp [dehomZ]

theorem dehomZ_cubic : dehomZ W W.toProjective.polynomial = 0 := by
  simp only [dehomZ, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination equation_xC_yC W

theorem dehomZ_surjective : Function.Surjective (dehomZ W) := by
  intro t
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective t
  induction q using Polynomial.induction_on with
  | C a =>
    induction a using Polynomial.induction_on with
    | C r => exact ⟨C r, by simp [dehomZ]; rfl⟩
    | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      exact ⟨P + Q, by rw [map_add, hP, hQ, Polynomial.C_add, map_add]⟩
    | monomial n r _ =>
      refine ⟨C r * X 0 ^ (n + 1), ?_⟩
      simp only [dehomZ, map_mul, map_pow, coe_eval₂Hom, eval₂_C, eval₂_X]
      simp only [Matrix.cons_val_zero, xC, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul,
        Polynomial.C_pow, map_mul, map_pow]
      rfl
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by rw [map_add, hP, hQ, map_add]⟩
  | monomial n a hp =>
    obtain ⟨P, hP⟩ := hp
    refine ⟨P * X 1, ?_⟩
    rw [map_mul, hP, pow_succ, ← mul_assoc, map_mul (AdjoinRoot.mk _)]
    simp [dehomZ, yC]

theorem val_scale_eq_zero_z :
    (W.toAffine.polynomial.eval₂ (Polynomial.eval₂RingHom (scalarAway W 2) (frac W 2 0))
      (frac W 2 1)).val = 0 := by
  have h0 := scale_eq_zero_of_mem W (j := 2)
  have hu : algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 2) * vinv W 2 = 1 :=
    IsLocalization.Away.mul_invSelf _
  rw [← HomogeneousLocalization.algebraMap_apply, Polynomial.hom_eval₂,
    HomogeneousLocalization.algebraMap_apply, val_frac]
  simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
    RingHom.comp_apply, Polynomial.coe_eval₂RingHom, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    val_frac, val_scalarAway]
  simp only [scale, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C, RingHom.comp_apply, π_C] at h0
  set u := vinv W 2
  set x := algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 0)
  set y := algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 1)
  set s := algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 2) * u
  have hs : s = 1 := hu
  linear_combination h0 - ((y * u) ^ 2 + algebraMap (HomRing W) _ (algebraMap R _ W.a₁) * (x * u) * (y * u) +
    algebraMap (HomRing W) _ (algebraMap R _ W.a₃) * (y * u) * (s + 1) -
    algebraMap (HomRing W) _ (algebraMap R _ W.a₂) * (x * u) ^ 2 -
    algebraMap (HomRing W) _ (algebraMap R _ W.a₄) * (x * u) * (s + 1) -
    algebraMap (HomRing W) _ (algebraMap R _ W.a₆) * (s ^ 2 + s + 1)) * hs

noncomputable def coordToAwayZ : W.toAffine.CoordinateRing →+* Away (homGrading W) (var W 2) :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (scalarAway W 2) (frac W 2 0)) (frac W 2 1)
    (HomogeneousLocalization.val_injective _ (by rw [val_scale_eq_zero_z, val_zero]))

theorem val_coordToAwayZ_dehomZ (P : MvPolynomial (Fin 3) R) :
    (coordToAwayZ W (dehomZ W P)).val = scale (π W) 2 P := by
  have hu : algebraMap (HomRing W) (Localization.Away (var W 2)) (var W 2) * vinv W 2 = 1 :=
    IsLocalization.Away.mul_invSelf _
  change ((algebraMap (Away (homGrading W) (var W 2)) (Localization.Away (var W 2))).comp
    ((coordToAwayZ W).comp (dehomZ W))) P = scale (π W) 2 P
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_C, scale]
    rw [show algebraMap R W.toAffine.CoordinateRing r = AdjoinRoot.of _ (Polynomial.C r) from rfl,
      coordToAwayZ, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      HomogeneousLocalization.algebraMap_apply, val_scalarAway]
    rfl
  · intro k
    fin_cases k
    · simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, xC]
      rw [show AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X) =
          AdjoinRoot.of _ Polynomial.X from rfl, coordToAwayZ, AdjoinRoot.lift_of,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, HomogeneousLocalization.algebraMap_apply,
        val_frac]
    · simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, yC]
      rw [coordToAwayZ, AdjoinRoot.lift_root, HomogeneousLocalization.algebraMap_apply, val_frac]
    · simp only [RingHom.comp_apply, dehomZ, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, map_one]
      exact hu.symm

noncomputable def chartZEquiv : Away (homGrading W) (var W 2) ≃+* W.toAffine.CoordinateRing :=
  awayEquiv W (dehomZ W) (dehomZ_X_two W) (dehomZ_cubic W) (dehomZ_surjective W) (coordToAwayZ W)
    (val_coordToAwayZ_dehomZ W)

end ChartZ

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section ChartY

noncomputable def dehomY : MvPolynomial (Fin 3) R →+* InfChart W :=
  eval₂Hom (algebraMap R _) ![xI W, 1, zI W]

theorem dehomY_X_one : dehomY W (X 1) = 1 := by simp [dehomY]

theorem dehomY_cubic : dehomY W W.toProjective.polynomial = 0 := by
  simp only [dehomY, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (-1 : InfChart W) * equation_xI_zI W

theorem dehomY_surjective : Function.Surjective (dehomY W) := by
  intro t
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective t
  induction q using Polynomial.induction_on with
  | C a =>
    induction a using Polynomial.induction_on with
    | C r => exact ⟨C r, by simp [dehomY]; rfl⟩
    | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      exact ⟨P + Q, by rw [map_add, hP, hQ, Polynomial.C_add, map_add]⟩
    | monomial n r _ =>
      refine ⟨C r * X 2 ^ (n + 1), ?_⟩
      simp only [dehomY, map_mul, map_pow, coe_eval₂Hom, eval₂_C, eval₂_X]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, zI]
      rfl
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨P + Q, by rw [map_add, hP, hQ, map_add]⟩
  | monomial n a hp =>
    obtain ⟨P, hP⟩ := hp
    refine ⟨P * X 0, ?_⟩
    rw [map_mul, hP, pow_succ, ← mul_assoc, map_mul (AdjoinRoot.mk _)]
    simp [dehomY, xI]

theorem val_scale_eq_zero_y :
    ((infPolynomial W).eval₂ (Polynomial.eval₂RingHom (scalarAway W 1) (frac W 1 2))
      (frac W 1 0)).val = 0 := by
  have h0 := scale_eq_zero_of_mem W (j := 1)
  have hu : algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 1) * vinv W 1 = 1 :=
    IsLocalization.Away.mul_invSelf _
  rw [← HomogeneousLocalization.algebraMap_apply, Polynomial.hom_eval₂,
    HomogeneousLocalization.algebraMap_apply, val_frac]
  simp only [infPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
    RingHom.comp_apply, Polynomial.coe_eval₂RingHom, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.val_sub, val_frac, val_scalarAway]
  simp only [scale, WeierstrassCurve.Projective.polynomial, map_sub, map_add, map_mul, map_pow,
    coe_eval₂Hom, eval₂_X, eval₂_C, RingHom.comp_apply, π_C] at h0
  set u := vinv W 1
  set x := algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 0)
  set z := algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 2)
  set s := algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 1) * u
  have hs : s = 1 := hu
  linear_combination -h0 + ((s + 1) * (z * u) +
    algebraMap (HomRing W) _ (algebraMap R _ W.a₁) * (x * u) * (z * u) +
    algebraMap (HomRing W) _ (algebraMap R _ W.a₃) * (z * u) ^ 2) * hs

noncomputable def infToAwayY : InfChart W →+* Away (homGrading W) (var W 1) :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (scalarAway W 1) (frac W 1 2)) (frac W 1 0)
    (HomogeneousLocalization.val_injective _ (by rw [val_scale_eq_zero_y, val_zero]))

theorem val_infToAwayY_dehomY (P : MvPolynomial (Fin 3) R) :
    (infToAwayY W (dehomY W P)).val = scale (π W) 1 P := by
  have hu : algebraMap (HomRing W) (Localization.Away (var W 1)) (var W 1) * vinv W 1 = 1 :=
    IsLocalization.Away.mul_invSelf _
  change ((algebraMap (Away (homGrading W) (var W 1)) (Localization.Away (var W 1))).comp
    ((infToAwayY W).comp (dehomY W))) P = scale (π W) 1 P
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_C, scale]
    rw [show algebraMap R (InfChart W) r = AdjoinRoot.of _ (Polynomial.C r) from rfl,
      infToAwayY, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      HomogeneousLocalization.algebraMap_apply, val_scalarAway]
    rfl
  · intro k
    fin_cases k
    · simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, xI]
      rw [infToAwayY, AdjoinRoot.lift_root, HomogeneousLocalization.algebraMap_apply, val_frac]
    · simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, map_one]
      exact hu.symm
    · simp only [RingHom.comp_apply, dehomY, coe_eval₂Hom, eval₂_X, scale]
      simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, zI]
      rw [infToAwayY, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        HomogeneousLocalization.algebraMap_apply, val_frac]

noncomputable def chartYEquiv : Away (homGrading W) (var W 1) ≃+* InfChart W :=
  awayEquiv W (dehomY W) (dehomY_X_one W) (dehomY_cubic W) (dehomY_surjective W) (infToAwayY W)
    (val_infToAwayY_dehomY W)

end ChartY

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Charts

theorem awayTo_scalarAway {j : Fin 3} {T : Type u} [CommRing T] (ψ : MvPolynomial (Fin 3) R →+* T)
    (hψ1 : ψ (X j) = 1) (hψF : ψ W.toProjective.polynomial = 0) (r : R) :
    awayTo W ψ hψ1 hψF (scalarAway W j r) = ψ (C r) := by
  simp only [awayTo, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, val_scalarAway]
  rw [Localization.awayLift, IsLocalization.Away.lift_eq]
  rfl

theorem chartZEquiv_scalarAway (r : R) : chartZEquiv W (scalarAway W 2 r) = algebraMap R _ r := by
  rw [chartZEquiv, awayEquiv_apply, awayTo_scalarAway]
  simp [dehomZ]

theorem chartYEquiv_scalarAway (r : R) : chartYEquiv W (scalarAway W 1 r) = algebraMap R _ r := by
  rw [chartYEquiv, awayEquiv_apply, awayTo_scalarAway]
  simp [dehomY]

theorem chartι_toSpec (j : Fin 3) :
    Proj.awayι (homGrading W) (var W j) (var_mem W j) one_pos ≫ toSpec W =
      Spec.map (CommRingCat.ofHom (scalarAway W j)) := by
  rw [toSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

noncomputable def chartZ : Spec (.of W.toAffine.CoordinateRing) ⟶ Curve W :=
  Spec.map (CommRingCat.ofHom (chartZEquiv W).toRingHom) ≫ chartZι W

noncomputable def chartY : Spec (.of (InfChart W)) ⟶ Curve W :=
  Spec.map (CommRingCat.ofHom (chartYEquiv W).toRingHom) ≫ chartYι W

instance : IsIso (Spec.map (CommRingCat.ofHom (chartZEquiv W).toRingHom)) := by
  have : IsIso (CommRingCat.ofHom (chartZEquiv W).toRingHom) :=
    (chartZEquiv W).toCommRingCatIso.isIso_hom
  infer_instance

instance : IsIso (Spec.map (CommRingCat.ofHom (chartYEquiv W).toRingHom)) := by
  have : IsIso (CommRingCat.ofHom (chartYEquiv W).toRingHom) :=
    (chartYEquiv W).toCommRingCatIso.isIso_hom
  infer_instance

instance : IsOpenImmersion (chartZι W) := by unfold chartZι; infer_instance
instance : IsOpenImmersion (chartYι W) := by unfold chartYι; infer_instance
instance : IsOpenImmersion (chartZ W) := by unfold chartZ; infer_instance
instance : IsOpenImmersion (chartY W) := by unfold chartY; infer_instance

end Charts

end Weierstrass

end GroundTheory.Arith.Modular
