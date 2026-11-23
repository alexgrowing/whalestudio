import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsNorm

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

section Infinity

omit [Field F] in
private theorem two_nsmul_add_le {u v w : WithBot ℕ} (h : u ≤ max v w) (c : WithBot ℕ) :
    2 • u + c ≤ max (2 • v + c) (2 • w + c) := by
  rcases le_total v w with hvw | hvw
  · rw [max_eq_right hvw] at h
    exact le_max_of_le_right (add_le_add (nsmul_le_nsmul_right h 2) le_rfl)
  · rw [max_eq_left hvw] at h
    exact le_max_of_le_left (add_le_add (nsmul_le_nsmul_right h 2) le_rfl)

theorem degree_norm_add_le (a b : W.toAffine.CoordinateRing) :
    (Algebra.norm F[X] (a + b)).degree ≤
      max (Algebra.norm F[X] a).degree (Algebra.norm F[X] b).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  obtain ⟨p', q', rfl⟩ := exists_smul_basis_eq b
  have hs : p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X +
      (p' • 1 + q' • AdjoinRoot.mk W.toAffine.polynomial X) =
        (p + p') • 1 + (q + q') • AdjoinRoot.mk W.toAffine.polynomial X := by
    rw [add_smul, add_smul]; abel
  rw [hs, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  have h1 := two_nsmul_add_le (degree_add_le p p') 0
  have h2 := two_nsmul_add_le (degree_add_le q q') 3
  simp only [add_zero] at h1
  exact max_le (h1.trans (max_le_max (le_max_left _ _) (le_max_left _ _)))
    (h2.trans (max_le_max (le_max_right _ _) (le_max_right _ _)))

theorem norm_coordinateRing_ne_zero {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    Algebra.norm F[X] a ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr ha

noncomputable def valuationInftyCoord : Valuation W.toAffine.CoordinateRing ℤᵐ⁰ where
  toFun a := if a = 0 then 0 else exp ((Algebra.norm F[X] a).natDegree : ℤ)
  map_zero' := if_pos rfl
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, map_mul,
      natDegree_mul (norm_coordinateRing_ne_zero W ha) (norm_coordinateRing_ne_zero W hb),
      Nat.cast_add, exp_add]
  map_add_le_max' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    by_cases hab : a + b = 0
    · simp [hab]
    simp only [if_neg ha, if_neg hb, if_neg hab]
    have hd := degree_norm_add_le W a b
    rw [degree_eq_natDegree (norm_coordinateRing_ne_zero W hab),
      degree_eq_natDegree (norm_coordinateRing_ne_zero W ha),
      degree_eq_natDegree (norm_coordinateRing_ne_zero W hb)] at hd
    rcases le_max_iff.mp hd with h | h
    · exact le_max_of_le_left (exp_le_exp.mpr (by exact_mod_cast WithBot.coe_le_coe.mp h))
    · exact le_max_of_le_right (exp_le_exp.mpr (by exact_mod_cast WithBot.coe_le_coe.mp h))

theorem valuationInftyCoord_apply {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    valuationInftyCoord W a = exp ((Algebra.norm F[X] a).natDegree : ℤ) := if_neg ha

theorem valuationInftyCoord_ne_zero {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    valuationInftyCoord W a ≠ 0 := by
  rw [valuationInftyCoord_apply W ha]; exact exp_ne_zero

noncomputable def valuationInfty : Valuation W.toAffine.FunctionField ℤᵐ⁰ :=
  (valuationInftyCoord W).extendToLocalization (S := W.toAffine.CoordinateRing⁰)
    (fun _ hr => Set.mem_compl (valuationInftyCoord_ne_zero W (nonZeroDivisors.ne_zero hr)))
    W.toAffine.FunctionField

theorem valuationInfty_algebraMap (a : W.toAffine.CoordinateRing) :
    valuationInfty W (algebraMap _ W.toAffine.FunctionField a) = valuationInftyCoord W a :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ a

noncomputable def ordInfty (f : W.toAffine.FunctionField) : ℤ :=
  -log (valuationInfty W f)

theorem valuationInfty_ne_zero {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    valuationInfty W f ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hf

theorem valuationInfty_eq_exp {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    valuationInfty W f = exp (-ordInfty W f) := by
  rw [ordInfty, neg_neg, exp_log (valuationInfty_ne_zero W hf)]

theorem ordInfty_algebraMap {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    ordInfty W (algebraMap _ W.toAffine.FunctionField a) =
      -((Algebra.norm F[X] a).natDegree : ℤ) := by
  rw [ordInfty, valuationInfty_algebraMap, valuationInftyCoord_apply W ha, log_exp]

theorem ordInfty_mul {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f * g) = ordInfty W f + ordInfty W g := by
  rw [ordInfty, ordInfty, ordInfty, map_mul,
    log_mul (valuationInfty_ne_zero W hf) (valuationInfty_ne_zero W hg), neg_add]

theorem ordInfty_inv (f : W.toAffine.FunctionField) : ordInfty W f⁻¹ = -ordInfty W f := by
  rw [ordInfty, ordInfty, map_inv₀, log_inv]

theorem ordInfty_div {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f / g) = ordInfty W f - ordInfty W g := by
  rw [div_eq_mul_inv, ordInfty_mul W hf (inv_ne_zero hg), ordInfty_inv, sub_eq_add_neg]

theorem ordInfty_algebraMap_const {c : F} (hc : c ≠ 0) :
    ordInfty W (algebraMap F W.toAffine.FunctionField c) = 0 := by
  have h : algebraMap F W.toAffine.FunctionField c =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap F[X] W.toAffine.CoordinateRing (C c)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField c,
      algebraMap_eq]
  have hc' : algebraMap F[X] W.toAffine.CoordinateRing (C c) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr (C_ne_zero.mpr hc)
  rw [h, ordInfty_algebraMap W hc', Algebra.norm_algebraMap, finrank_coordinateRing, ← C_pow,
    natDegree_C, Nat.cast_zero, neg_zero]

theorem ordInfty_X :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial (C X))) = -2 := by
  have hx : AdjoinRoot.mk W.toAffine.polynomial (C X) =
      algebraMap F[X] W.toAffine.CoordinateRing X := by
    simp only [AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  have h0 : algebraMap F[X] W.toAffine.CoordinateRing X ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr X_ne_zero
  rw [hx, ordInfty_algebraMap W h0, Algebra.norm_algebraMap, finrank_coordinateRing,
    natDegree_X_pow]
  norm_num

theorem ordInfty_Y :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial X)) = -3 := by
  have hy : AdjoinRoot.mk W.toAffine.polynomial X =
      (0 : F[X]) • (1 : W.toAffine.CoordinateRing) +
        (1 : F[X]) • AdjoinRoot.mk W.toAffine.polynomial X := by
    rw [zero_smul, one_smul, zero_add]
  have hdeg := degree_norm_smul_basis (W' := W.toAffine) (0 : F[X]) 1
  rw [← hy, degree_zero, degree_one] at hdeg
  have hdeg' : (Algebra.norm F[X] (AdjoinRoot.mk W.toAffine.polynomial X)).degree = 3 := by
    rw [hdeg]; rfl
  have h0 : AdjoinRoot.mk W.toAffine.polynomial X ≠ 0 := by
    rw [← basis_one]
    exact (CoordinateRing.basis W.toAffine).ne_zero 1
  rw [ordInfty_algebraMap W h0, natDegree_eq_of_degree_eq_some hdeg']
  norm_num

theorem ordInfty_X_div_Y :
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial (C X)) /
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.mk W.toAffine.polynomial X)) = 1 := by
  have hne : ∀ f : W.toAffine.FunctionField, ordInfty W f ≠ 0 → f ≠ 0 := by
    rintro f hf rfl
    exact hf (by simp [ordInfty])
  rw [ordInfty_div W (hne _ (by rw [ordInfty_X]; norm_num)) (hne _ (by rw [ordInfty_Y]; norm_num)),
    ordInfty_X, ordInfty_Y]
  norm_num

end Infinity

section Affine

variable [IsAlgClosed F] [W.IsElliptic]

noncomputable def ordAtIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    (f : W.toAffine.FunctionField) : ℤ :=
  FractionalIdeal.count W.toAffine.FunctionField v
    (FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f)

omit [IsAlgClosed F] [W.IsElliptic] in
theorem spanSingleton_ne_zero {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ f ≠ 0 :=
  FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hf

theorem ordAtIdeal_mul (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordAtIdeal W v (f * g) = ordAtIdeal W v f + ordAtIdeal W v g := by
  rw [ordAtIdeal, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul _ _ (spanSingleton_ne_zero W hf) (spanSingleton_ne_zero W hg)]
  rfl

theorem ordAtIdeal_algebraMap (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    (a : W.toAffine.CoordinateRing) :
    ordAtIdeal W v (algebraMap _ W.toAffine.FunctionField a) =
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {a} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  rw [ordAtIdeal, FractionalIdeal.coeIdeal_span_singleton]

theorem valuation_eq_exp_neg_ordAtIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    v.valuation W.toAffine.FunctionField f = exp (-ordAtIdeal W v f) := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only at hf ⊢
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf (IsLocalization.mk'_zero _)
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hs' : algebraMap _ W.toAffine.FunctionField (s : W.toAffine.CoordinateRing) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ W.toAffine.FunctionField)).mpr hs
  have hsa : Ideal.span {a} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hss : Ideal.span {(s : W.toAffine.CoordinateRing)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hord := ordAtIdeal_mul W v hf hs'
  rw [IsLocalization.mk'_spec, ordAtIdeal_algebraMap, ordAtIdeal_algebraMap] at hord
  rw [HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.intValuation_if_neg _ ha,
    HeightOneSpectrum.intValuation_if_neg _ hs, ← FractionalIdeal.count_coe W.toAffine.FunctionField v hsa,
    ← FractionalIdeal.count_coe W.toAffine.FunctionField v hss, ← exp_sub]
  congr 1
  linarith

noncomputable def valuationPoint : W.toAffine.Point → Valuation W.toAffine.FunctionField ℤᵐ⁰
  | .zero => valuationInfty W
  | .some _ _ h => (heightOneOfNonsingular h).valuation W.toAffine.FunctionField

noncomputable def ordPoint : W.toAffine.Point → W.toAffine.FunctionField → ℤ
  | .zero => ordInfty W
  | .some _ _ h => ordAtIdeal W (heightOneOfNonsingular h)

theorem ordPoint_zero : ordPoint W 0 = ordInfty W := rfl

theorem ordPoint_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ordPoint W (.some x y h) = ordAtIdeal W (heightOneOfNonsingular h) := rfl

theorem valuationPoint_eq_exp (P : W.toAffine.Point) {f : W.toAffine.FunctionField}
    (hf : f ≠ 0) : valuationPoint W P f = exp (-ordPoint W P f) := by
  cases P with
  | zero => exact valuationInfty_eq_exp W hf
  | some x y h => exact valuation_eq_exp_neg_ordAtIdeal W _ hf

theorem ordPoint_mul (P : W.toAffine.Point) {f g : W.toAffine.FunctionField} (hf : f ≠ 0)
    (hg : g ≠ 0) : ordPoint W P (f * g) = ordPoint W P f + ordPoint W P g := by
  cases P with
  | zero => exact ordInfty_mul W hf hg
  | some x y h => exact ordAtIdeal_mul W _ hf hg

theorem exists_valuationPoint_eq_exp_neg_one (P : W.toAffine.Point) :
    ∃ t : W.toAffine.FunctionField, valuationPoint W P t = exp (-1) := by
  cases P with
  | zero =>
    refine ⟨algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial (C X)) /
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.mk W.toAffine.polynomial X), ?_⟩
    rw [valuationPoint, valuationInfty_eq_exp W, ordInfty_X_div_Y]
    intro h0
    have := ordInfty_X_div_Y W
    rw [h0] at this
    simp [ordInfty] at this
  | some x y h => exact HeightOneSpectrum.valuation_exists_uniformizer _ _

end Affine

end GroundTheory.Arith.Abelian
