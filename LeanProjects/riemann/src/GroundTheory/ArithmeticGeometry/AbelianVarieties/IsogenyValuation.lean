import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero IntermediateField

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F]

section Infinity

variable {W : WeierstrassCurve F}

theorem eq_valuationInfty_pow_of_genX (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {a : ℕ} (ha : 0 < a)
    (hx : w (genX W) = exp (2 * (a : ℤ))) (f : W.toAffine.FunctionField) :
    w f = valuationInfty W f ^ a := by
  have hk : (0 : ℤ) < 2 * a := by positivity
  obtain ⟨m, hm, hm3⟩ := valuation_genY_of_one_lt w hF hk hx
  have hm' : m = 3 * a := by linarith
  subst hm'
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hA : ∀ c : W.toAffine.CoordinateRing,
      w (algebraMap _ W.toAffine.FunctionField c) =
        valuationInfty W (algebraMap _ W.toAffine.FunctionField c) ^ a := by
    intro c
    rcases eq_or_ne c 0 with rfl | hc
    · simp [zero_pow ha.ne']
    rw [valuationInfty_algebraMap, valuationInftyCoord_apply W hc, ← exp_nsmul]
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq c
    rw [algebraMap_smul_basis]
    rcases eq_or_ne q 0 with rfl | hq
    · have hp : p ≠ 0 := by rintro rfl; simp at hc
      rw [natDegree_norm_smul_basis_of_q_eq_zero, map_zero, zero_mul, add_zero,
        valuation_poly_of_one_lt w hF hk hx hp]
      congr 1; push_cast; ring
    · have hwQy : w (algebraMap F[X] W.toAffine.FunctionField q * genY W) =
          exp (2 * a * (q.natDegree : ℤ) + 3 * a) := by
        rw [Valuation.map_mul, valuation_poly_of_one_lt w hF hk hx hq, hm, ← exp_add]
        congr 1; ring
      rcases eq_or_ne p 0 with rfl | hp
      · rw [natDegree_norm_smul_basis_of_p_eq_zero hq, map_zero, zero_add, hwQy]
        congr 1; push_cast; ring
      · rw [natDegree_norm_smul_basis_of_ne_zero hp hq]
        have hwP := valuation_poly_of_one_lt w hF hk hx hp
        have hapos : (0 : ℤ) < a := by exact_mod_cast ha
        rcases lt_or_gt_of_ne (show (2 * p.natDegree : ℤ) ≠ 2 * q.natDegree + 3 by omega) with
          hlt | hlt
        · rw [Valuation.map_add_eq_of_lt_right _ (by rw [hwP, hwQy, exp_lt_exp]; nlinarith), hwQy,
            max_eq_right (by omega)]
          congr 1; push_cast; ring
        · rw [Valuation.map_add_eq_of_lt_left _ (by rw [hwP, hwQy, exp_lt_exp]; nlinarith), hwP,
            max_eq_left (by omega)]
          congr 1; push_cast; ring
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hspec := IsLocalization.mk'_spec W.toAffine.FunctionField c s
  have h1 := congrArg w hspec
  have h2 := congrArg (fun g => valuationInfty W g ^ a) hspec
  rw [Valuation.map_mul, hA, hA] at h1
  rw [Valuation.map_mul, mul_pow] at h2
  have hvs : valuationInfty W (algebraMap _ W.toAffine.FunctionField
      (s : W.toAffine.CoordinateRing)) ^ a ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs))
  exact mul_right_cancel₀ hvs (h1.trans h2.symm)

omit [Field F] in
theorem genX_ne_zero' [Field F] (W : WeierstrassCurve F) : genX W ≠ 0 := by
  intro h
  apply transcendental_genX W
  rw [h]
  exact isAlgebraic_zero

theorem exists_eq_valuationInfty_pow (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : 1 < w (genX W)) : ∃ e : ℕ, 0 < e ∧ ∀ f, w f = valuationInfty W f ^ e := by
  have hx0 : w (genX W) ≠ 0 := (Valuation.ne_zero_iff _).mpr (genX_ne_zero' W)
  set k := log (w (genX W))
  have hxk : w (genX W) = exp k := (exp_log hx0).symm
  have hk : 0 < k := by
    rw [hxk, ← exp_zero, exp_lt_exp] at hx; exact hx
  obtain ⟨m, -, hm3⟩ := valuation_genY_of_one_lt w hF hk hxk
  refine ⟨(m - k).toNat, by omega, eq_valuationInfty_pow_of_genX w hF (by omega) ?_⟩
  rw [hxk]
  congr 1
  omega

end Infinity

section Classify

variable {W : WeierstrassCurve F} [IsAlgClosed F] [W.IsElliptic]

theorem valuationPoint_pointOfIdeal [DecidableEq F] (v : HeightOneSpectrum W.toAffine.CoordinateRing) :
    valuationPoint W (pointOfIdeal W v) = v.valuation W.toAffine.FunctionField := by
  obtain ⟨h, e⟩ : ∃ h : W.toAffine.Nonsingular _ _, pointOfIdeal W v = .some _ _ h := ⟨_, rfl⟩
  have hv : heightOneOfNonsingular h = v := by
    apply pointOfIdeal_injective W
    rw [pointOfIdeal_heightOneOfNonsingular, e]
  rw [e]
  show (heightOneOfNonsingular h).valuation _ = _
  rw [hv]

theorem exists_valuationPoint_pow [DecidableEq F] (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hnt : ∃ f, f ≠ 0 ∧ w f ≠ 1) :
    ∃ (P : W.toAffine.Point) (e : ℕ), 0 < e ∧ ∀ f, w f = valuationPoint W P f ^ e := by
  by_cases hx : 1 < w (genX W)
  · obtain ⟨e, he, h⟩ := exists_eq_valuationInfty_pow w hF hx
    exact ⟨0, e, he, h⟩
  · obtain ⟨v, -, e, he, h⟩ := exists_eq_pow_valuation_of_le_one w hF (not_lt.mp hx) hnt
    exact ⟨pointOfIdeal W v, e, he, fun f => by rw [valuationPoint_pointOfIdeal, h]⟩

theorem valuationPoint_genX_le_one {P : W.toAffine.Point} (hP : P ≠ 0) :
    valuationPoint W P (genX W) ≤ 1 := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    show (heightOneOfNonsingular h).valuation _ (algebraMap _ _ _) ≤ 1
    exact HeightOneSpectrum.valuation_le_one _ _

theorem valuationPoint_zero_genX : valuationPoint W 0 (genX W) = exp 2 := valuationInfty_genX W

theorem eq_zero_of_one_lt_valuationPoint_genX {P : W.toAffine.Point}
    (h : 1 < valuationPoint W P (genX W)) : P = 0 := by
  by_contra hP
  exact absurd (valuationPoint_genX_le_one hP) (not_le.mpr h)

theorem eq_of_valuationPoint_pow_eq [DecidableEq F] {P Q : W.toAffine.Point} {e e' : ℕ} (he : 0 < e)
    (h : ∀ f, valuationPoint W P f ^ e = valuationPoint W Q f ^ e') : P = Q := by
  have he' : e' ≠ 0 := by
    rintro rfl
    have := h 0
    rw [map_zero, zero_pow he.ne', pow_zero] at this
    exact zero_ne_one this

  have h' : ∀ f, valuationPoint W 0 f ^ e = valuationPoint W (Q - P) f ^ e' := by
    intro f
    have := h (translate W (-P) f)
    rwa [valuationPoint_translate, valuationPoint_translate, add_neg_cancel, ← sub_eq_add_neg] at this
  have hx := h' (genX W)
  rw [valuationPoint_zero_genX, ← exp_nsmul] at hx
  have hgt : 1 < valuationPoint W (Q - P) (genX W) := by
    by_contra hle
    rw [not_lt] at hle
    have : valuationPoint W (Q - P) (genX W) ^ e' ≤ 1 := pow_le_one' hle _
    rw [← hx, ← exp_zero, exp_le_exp] at this
    simp only [nsmul_eq_mul] at this
    have : (0 : ℤ) < e := by exact_mod_cast he
    linarith
  have := eq_zero_of_one_lt_valuationPoint_genX hgt
  rw [sub_eq_zero] at this
  exact this.symm

theorem eq_of_valuationPoint_pow_eq_pow (P : W.toAffine.Point) {e e' : ℕ}
    (h : ∀ f, valuationPoint W P f ^ e = valuationPoint W P f ^ e') : e = e' := by
  obtain ⟨t, ht⟩ := exists_valuationPoint_eq_exp_neg_one W P
  have := h t
  rw [ht, ← exp_nsmul, ← exp_nsmul, exp_inj] at this
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_inj] at this
  exact_mod_cast this

end Classify

section Isogeny

variable [IsAlgClosed F] [DecidableEq F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic]
  [E'.IsElliptic] [E''.IsElliptic]

omit [IsAlgClosed F] [DecidableEq F] in

theorem valuation_le_one_of_isIntegral {K : Type*} [Field K] [Algebra F K]
    (M : IntermediateField F K) (v : Valuation K ℤᵐ⁰) (hM : ∀ m : M, v (m : K) ≤ 1) {z : K}
    (hz : IsIntegral M z) : v z ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  have hz0 : z ≠ 0 := by rintro rfl; simp at hgt
  have hvz : v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  set k := log (v z)
  have hk : v z = exp k := (exp_log hvz).symm
  have hkpos : 0 < k := by rw [hk, ← exp_zero, exp_lt_exp] at hgt; exact hgt
  have hmon : (minpoly M z).Monic := minpoly.monic hz
  have h0 := minpoly.aeval M z
  rw [hmon.as_sum] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  set n := (minpoly M z).natDegree
  have hpow : ∀ i : ℕ, v z ^ i = exp (i * k) := fun i => by
    rw [hk, ← exp_nsmul, nsmul_eq_mul]
  have hsum : v (∑ i ∈ Finset.range n, algebraMap M K ((minpoly M z).coeff i) * z ^ i) <
      v (z ^ n) := by
    rw [Valuation.map_pow, hpow]
    apply Valuation.map_sum_lt _ exp_ne_zero
    intro i hi
    rw [Valuation.map_mul, Valuation.map_pow, hpow]
    calc v (algebraMap M K ((minpoly M z).coeff i)) * exp (i * k) ≤ 1 * exp (i * k) :=
          mul_le_mul_left (hM _) _
      _ < exp (n * k) := by
          rw [one_mul, exp_lt_exp]
          have : (i : ℤ) < n := by exact_mod_cast Finset.mem_range.mp hi
          nlinarith
  have := Valuation.map_add_eq_of_lt_left v hsum
  rw [h0, map_zero, Valuation.map_pow, hpow] at this
  exact exp_ne_zero this.symm

theorem valuationPoint_zero_eq (f : E.toAffine.FunctionField) :
    valuationPoint E 0 f = valuationInfty E f := rfl

namespace Isogeny

theorem exists_point_valuation_comap (φ : Isogeny E E') :
    ∃ (Q : E'.toAffine.Point) (e : ℕ), 0 < e ∧ ∀ R f,
      valuationPoint E R (φ.comap f) = valuationPoint E' (Q + φ.pointMap R) f ^ e := by
  let w : Valuation E'.toAffine.FunctionField ℤᵐ⁰ := (valuationPoint E 0).comap φ.comap.toRingHom
  have hw : ∀ f, w f = valuationPoint E 0 (φ.comap f) := fun f => rfl
  have hF : ∀ c : F, c ≠ 0 → w (algebraMap F E'.toAffine.FunctionField c) = 1 := by
    intro c hc
    rw [hw, AlgHom.commutes, valuationPoint_zero_eq, valuationInfty_algebraMap_const_eq_one E hc]
  have hnt : ∃ f, f ≠ 0 ∧ w f ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hM : ∀ m : φ.comap.fieldRange, valuationPoint E 0 (m : E.toAffine.FunctionField) ≤ 1 := by
      rintro ⟨m, f, rfl⟩
      by_cases hf : f = 0
      · simp [hf]
      · exact (hcon f hf).le
    have := φ.finiteDimensional
    have hint : IsIntegral φ.comap.fieldRange (genX E) := IsIntegral.of_finite _ _
    have := valuation_le_one_of_isIntegral _ _ hM hint
    rw [valuationPoint_zero_genX, ← exp_zero, exp_le_exp] at this
    omega
  obtain ⟨Q, e, he, hQ⟩ := exists_valuationPoint_pow w hF hnt
  refine ⟨Q, e, he, fun R f => ?_⟩
  have h1 : valuationPoint E R (φ.comap f) = valuationPoint E 0 (translate E R (φ.comap f)) := by
    rw [valuationPoint_translate, zero_add]
  rw [h1, ← AlgHom.comp_apply, ← φ.comap_comp_translate, AlgHom.comp_apply, ← hw, hQ,
    valuationPoint_translate]

end Isogeny

theorem one_lt_valuationPoint_mulIsogeny_x {n : ℤ} (hn : n ≠ 0) :
    1 < valuationPoint E 0 ((mulIsogeny E n hn).comap (genX E)) := by
  have hvF : ∀ c : F, c ≠ 0 → valuationInfty E (algebraMap F E.toAffine.FunctionField c) = 1 :=
    fun c hc => valuationInfty_algebraMap_const_eq_one E hc
  have hΦ0 : E.Φ n ≠ 0 := by
    intro h
    have := E.natDegree_Φ n
    rw [h, natDegree_zero] at this
    have : 0 < n.natAbs ^ 2 := by have := Int.natAbs_pos.mpr hn; positivity
    omega
  have hΨ0 : E.ΨSq n ≠ 0 := ΨSq_ne_zero_of_ne_zero E hn
  have hΦ := valuation_poly_of_one_lt (valuationInfty E) hvF two_pos (valuationInfty_genX E) hΦ0
  have hΨ := valuation_poly_of_one_lt (valuationInfty E) hvF two_pos (valuationInfty_genX E) hΨ0
  rw [E.natDegree_Φ n] at hΦ
  have hle := natDegree_ΨSq_le E n
  have hpos : 0 < n.natAbs ^ 2 := by have := Int.natAbs_pos.mpr hn; positivity
  rw [Isogeny.comap_genX, mulIsogeny_alt, aeval_genX, aeval_genX, valuationPoint_zero_eq, map_div₀,
    hΦ, hΨ, ← exp_sub, ← exp_zero, exp_lt_exp]
  have : ((E.ΨSq n).natDegree : ℤ) < (n.natAbs ^ 2 : ℕ) := by
    have : (E.ΨSq n).natDegree < n.natAbs ^ 2 := by omega
    exact_mod_cast this
  push_cast at this ⊢
  linarith

namespace Isogeny

theorem comp_mulIsogeny_two (φ : Isogeny E E') :
    φ.comp (mulIsogeny E 2 two_ne_zero) = (mulIsogeny E' 2 two_ne_zero).comp φ := by
  apply ext'
  have h2 : (mulIsogeny E 2 two_ne_zero).1 = genericPoint E + genericPoint E := by
    rw [mulIsogeny_val, two_zsmul]
  have hG : IsGenPt E (genericPoint E + genericPoint E) := isGenPt_two_smul_genericPoint
  have e1 : (φ.comp (mulIsogeny E 2 two_ne_zero)).1 = φ.1 + φ.1 := by
    show φ.app (mulIsogeny E 2 two_ne_zero).1 _ = _
    rw [φ.app_congr h2 _ hG, φ.app_add isGenPt_genericPoint isGenPt_genericPoint hG,
      app_genericPoint']
  rw [e1, comp_val, mulIsogeny_val, map_zsmul, map_comap_genericPoint, two_zsmul]

theorem comap_comp_mulIsogeny_two (φ : Isogeny E E') :
    (mulIsogeny E 2 two_ne_zero).comap.comp φ.comap = φ.comap.comp (mulIsogeny E' 2 two_ne_zero).comap := by
  rw [← comap_comp, ← comap_comp, comp_mulIsogeny_two]

theorem mulIsogeny_two_valuation (E : WeierstrassCurve F) [E.IsElliptic] :
    ∃ e : ℕ, 0 < e ∧ ∀ R f, valuationPoint E R ((mulIsogeny E 2 two_ne_zero).comap f) =
      valuationPoint E ((2 : ℤ) • R) f ^ e := by
  obtain ⟨Q, e, he, hQ⟩ := (mulIsogeny E 2 two_ne_zero).exists_point_valuation_comap
  have hQ0 : Q = 0 := by
    have h := hQ 0 (genX E)
    have hlt := one_lt_valuationPoint_mulIsogeny_x (E := E) (n := 2) two_ne_zero
    rw [h, pointMap_mulIsogeny, smul_zero, add_zero] at hlt
    apply eq_zero_of_one_lt_valuationPoint_genX
    by_contra hle
    rw [not_lt] at hle
    exact absurd (pow_le_one' hle e) (not_le.mpr hlt)
  refine ⟨e, he, fun R f => ?_⟩
  rw [hQ, hQ0, zero_add, pointMap_mulIsogeny]

theorem exists_ramIdx (φ : Isogeny E E') : ∃ e : ℕ, 0 < e ∧ ∀ R f,
    valuationPoint E R (φ.comap f) = valuationPoint E' (φ.pointMap R) f ^ e := by
  obtain ⟨Q, e, he, hQ⟩ := φ.exists_point_valuation_comap
  suffices hQ0 : Q = 0 by
    refine ⟨e, he, fun R f => ?_⟩
    rw [hQ, hQ0, zero_add]
  obtain ⟨e₂, he₂, h₂⟩ := mulIsogeny_two_valuation E
  obtain ⟨e₂', he₂', h₂'⟩ := mulIsogeny_two_valuation E'
  have hφ0 : φ.pointMap 0 = 0 := map_zero φ.pointHom
  have key : ∀ f, valuationPoint E' Q f ^ (e * e₂) =
      valuationPoint E' ((2 : ℤ) • Q) f ^ (e₂' * e) := by
    intro f
    have h1 := h₂ 0 (φ.comap f)
    rw [smul_zero, hQ, hφ0, add_zero, ← pow_mul] at h1
    have h2 := DFunLike.congr_fun (comap_comp_mulIsogeny_two φ) f
    simp only [AlgHom.comp_apply] at h2
    rw [← h1, h2, hQ, hφ0, add_zero, h₂', ← pow_mul]
  have := eq_of_valuationPoint_pow_eq (Nat.mul_pos he he₂) key
  rw [two_zsmul, left_eq_add] at this
  exact this

noncomputable def ramIdx (φ : Isogeny E E') : ℕ := φ.exists_ramIdx.choose

theorem ramIdx_pos (φ : Isogeny E E') : 0 < φ.ramIdx := φ.exists_ramIdx.choose_spec.1

theorem valuationPoint_comap (φ : Isogeny E E') (R : E.toAffine.Point)
    (f : E'.toAffine.FunctionField) :
    valuationPoint E R (φ.comap f) = valuationPoint E' (φ.pointMap R) f ^ φ.ramIdx :=
  φ.exists_ramIdx.choose_spec.2 R f

theorem ordPoint_comap (φ : Isogeny E E') (R : E.toAffine.Point) {f : E'.toAffine.FunctionField}
    (hf : f ≠ 0) :
    ordPoint E R (φ.comap f) = φ.ramIdx * ordPoint E' (φ.pointMap R) f := by
  have hf' : φ.comap f ≠ 0 := (map_ne_zero_iff _ φ.comap.toRingHom.injective).mpr hf
  have h := φ.valuationPoint_comap R f
  rw [valuationPoint_eq_exp E R hf', valuationPoint_eq_exp E' _ hf, ← exp_nsmul, exp_inj,
    nsmul_eq_mul] at h
  linarith

theorem ramIdx_eq_of (φ : Isogeny E E') {e : ℕ} (R : E.toAffine.Point)
    (h : ∀ f, valuationPoint E R (φ.comap f) = valuationPoint E' (φ.pointMap R) f ^ e) :
    φ.ramIdx = e :=
  eq_of_valuationPoint_pow_eq_pow (φ.pointMap R) fun f => by rw [← h, valuationPoint_comap]

theorem ramIdx_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).ramIdx = ψ.ramIdx * φ.ramIdx := by
  apply ramIdx_eq_of _ 0
  intro f
  rw [comap_comp, AlgHom.comp_apply, valuationPoint_comap, valuationPoint_comap, pointMap_comp,
    ← pow_mul, mul_comm]

end Isogeny

end Isogeny

end GroundTheory.Arith.Abelian
