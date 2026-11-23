import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace ChartDomain

variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

abbrev Base : Type := Localization.Away (Ideal.Quotient.mk Q (X j))

def cx (e : ℕ) (l : Fin n) : MvPolynomial (Par e n) (Base Q j) :=
  C (algebraMap _ _ (Ideal.Quotient.mk Q (X l)))

def cinv (e : ℕ) : MvPolynomial (Par e n) (Base Q j) :=
  C (IsLocalization.Away.invSelf (Ideal.Quotient.mk Q (X j)))

theorem cx_mul_cinv : cx Q j e j * cinv Q j e = 1 := by
  rw [cx, cinv, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

def parVal : Par e n → MvPolynomial (Par e n) (Base Q j)
  | .inl (i, l) => X (.inl (i, l)) -
      if l = j then cinv Q j e * ∑ m, X (.inl (i, m)) * cx Q j e m else 0
  | .inr l => X (.inr l) -
      if l = j then cinv Q j e * (∑ m, X (.inr m) * cx Q j e m - 1) else 0

def κ (e : ℕ) : D →+* MvPolynomial (Par e n) (Base Q j) :=
  (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp ((Ideal.Quotient.mk Q).comp C))

def evalF (e : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* MvPolynomial (Par e n) (Base Q j) :=
  eval₂Hom (eval₂Hom (κ Q j e) (parVal Q j)) (cx Q j e)

theorem evalF_comp_map :
    (evalF Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)) =
      (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp (Ideal.Quotient.mk Q)) := by
  apply MvPolynomial.ringHom_ext
  · intro d; simp [evalF, κ]
  · intro l; simp [evalF, cx]

theorem secIdeal_le_ker :
    secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X ≤ RingHom.ker (evalF Q j e) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, evalF_comp_map]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inl (i, m)) * cx Q j e m)) * cx_mul_cinv Q j (e := e)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_one, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inr m) * cx Q j e m - 1)) * cx_mul_cinv Q j (e := e)

abbrev secI (e : ℕ) : Ideal (MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :=
  secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)

abbrev Sec (e : ℕ) : Type :=
  SecAlg (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)

abbrev xj (e : ℕ) : Sec Q e :=
  secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D) j

abbrev Chart (e : ℕ) : Type :=
  Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (X : Par e n → MvPolynomial (Par e n) D) j)

def toChart (e : ℕ) : MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* Chart Q j e :=
  algebraMap _ (Chart Q j e)

theorem toChart_apply (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toChart Q j e a =
      algebraMap (Sec Q e) (Chart Q j e) (Ideal.Quotient.mk (secI Q e) a) := rfl

def toPoly (e : ℕ) : Chart Q j e →+* MvPolynomial (Par e n) (Base Q j) :=
  IsLocalization.Away.lift (xj Q j e)
    (g := Ideal.Quotient.lift (secI Q e) (evalF Q j e) (fun _ ha => RingHom.mem_ker.mp (secIdeal_le_ker Q j ha))) (by
      simp only [xj, secCoord, Ideal.Quotient.lift_mk, evalF, coe_eval₂Hom, eval₂_X]
      exact IsUnit.of_mul_eq_one _ (cx_mul_cinv Q j (e := e)))

theorem toPoly_toChart (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toPoly Q j e (toChart Q j e a) = evalF Q j e a := by
  rw [toChart_apply, toPoly, IsLocalization.Away.lift_eq, Ideal.Quotient.lift_mk]

theorem toChart_eq_zero {e : ℕ} {a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)} (ha : a ∈ secI Q e) :
    toChart Q j e a = 0 := by
  rw [toChart_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

def quotToChart (e : ℕ) : MvPolynomial (Fin n) D ⧸ Q →+* Chart Q j e :=
  Ideal.Quotient.lift Q ((toChart Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (fun _ hq => toChart_eq_zero Q j (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))))

def baseToChart (e : ℕ) : Base Q j →+* Chart Q j e :=
  IsLocalization.Away.lift (Ideal.Quotient.mk Q (X j)) (g := quotToChart Q j e) (by
    rw [quotToChart, Ideal.Quotient.lift_mk, RingHom.comp_apply, map_X, toChart_apply]
    exact IsLocalization.Away.algebraMap_isUnit (xj Q j e))

def fromPoly (e : ℕ) : MvPolynomial (Par e n) (Base Q j) →+* Chart Q j e :=
  eval₂Hom (baseToChart Q j e) fun p => toChart Q j e (C (X p))

theorem baseToChart_mk (p : MvPolynomial (Fin n) D) :
    baseToChart Q j e (algebraMap _ (Base Q j) (Ideal.Quotient.mk Q p)) =
      toChart Q j e (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D) p) := by
  rw [baseToChart, IsLocalization.Away.lift_eq, quotToChart, Ideal.Quotient.lift_mk, RingHom.comp_apply]

theorem fromPoly_cx (l : Fin n) : fromPoly Q j e (cx Q j e l) = toChart Q j e (X l) := by
  rw [cx, fromPoly, coe_eval₂Hom, eval₂_C, baseToChart_mk, map_X]

theorem fromPoly_X (p : Par e n) : fromPoly Q j e (X p) = toChart Q j e (C (X p)) := by
  rw [fromPoly, coe_eval₂Hom, eval₂_X]

theorem fromPoly_secForm (i : Fin e) :
    fromPoly Q j e (∑ m, X (.inl (i, m)) * cx Q j e m) = 0 := by
  have hmem : secForm (X : Par e n → MvPolynomial (Par e n) D) i ∈ secI Q e :=
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  rw [← toChart_eq_zero Q j hmem]
  simp only [map_sum, map_mul, fromPoly_X, fromPoly_cx, secForm, linForm]

theorem fromPoly_chartForm :
    fromPoly Q j e (∑ m, X (.inr m) * cx Q j e m - 1) = 0 := by
  have hmem : chartForm (X : Par e n → MvPolynomial (Par e n) D) - 1 ∈ secI Q e :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← toChart_eq_zero Q j hmem]
  simp only [map_sum, map_mul, map_sub, map_one, fromPoly_X, fromPoly_cx, chartForm, linForm]

theorem fromPoly_toPoly_toChart :
    ((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e) = toChart Q j e := by
  apply MvPolynomial.ringHom_ext
  · intro c
    have h : (((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e)).comp C =
        (toChart Q j e).comp C := by
      apply MvPolynomial.ringHom_ext
      · intro d
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, κ, coe_eval₂Hom, eval₂_C, fromPoly,
          baseToChart_mk, map_C]
      · intro p
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_C, eval₂_X]
        rcases p with ⟨i, l⟩ | l
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_secForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_chartForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
    exact RingHom.congr_fun h c
  · intro l
    simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_X, fromPoly_cx]

theorem fromPoly_comp_toPoly : (fromPoly Q j e).comp (toPoly Q j e) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xj Q j e))
  apply Ideal.Quotient.ringHom_ext
  exact fromPoly_toPoly_toChart Q j

theorem toPoly_algebraMap (d : D) : toPoly Q j e (algebraMap D (Chart Q j e) d) = κ Q j e d := by
  rw [IsScalarTower.algebraMap_apply D (MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) (Chart Q j e),
    MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  exact (toPoly_toChart Q j e _).trans (by simp [evalF])

end ChartDomain

open ChartDomain in

theorem ChartDomain.proof : ChartDomain.Statement := by
  intro D _ _ n e Q j hQ hQD hXj
  have hxj : Ideal.Quotient.mk Q (X j) ≠ 0 := fun h => hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have : IsDomain (MvPolynomial (Fin n) D ⧸ Q) := Ideal.Quotient.isDomain Q
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hxj
  have : IsDomain (Base Q j) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (toPoly Q j e) :=
    Function.LeftInverse.injective (g := fromPoly Q j e) fun x => RingHom.congr_fun (fromPoly_comp_toPoly Q j) x
  refine ⟨Function.Injective.isDomain _ hinj, ?_⟩
  intro a b hab
  have h := congrArg (toPoly Q j e) hab
  rw [toPoly_algebraMap, toPoly_algebraMap] at h
  have h2 := IsLocalization.injective (Base Q j) hle (C_injective _ _ h)
  have h3 : C (a - b) ∈ Q := by rw [map_sub]; exact Ideal.Quotient.eq.mp h2
  exact sub_eq_zero.mp (hQD _ h3)

end

end GroundTheory.Heights₂.Heights.Vertical
