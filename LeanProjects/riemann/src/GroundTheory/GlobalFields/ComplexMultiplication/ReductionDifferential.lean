import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionDegree
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped Polynomial.Bivariate

universe u

section Delta

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDeriv (f : E.toAffine.FunctionField) : E.toAffine.FunctionField :=
  invCoeff E (D F E.toAffine.FunctionField f)

theorem invCoeff_smul_mul (c : E.toAffine.FunctionField) (η : KaehlerDifferential F E.toAffine.FunctionField) :
    invCoeff E (c • η) = c * invCoeff E η :=
  invCoeff_eq E (by rw [mul_smul, invCoeff_smul])

theorem invDeriv_add (f g : E.toAffine.FunctionField) :
    invDeriv E (f + g) = invDeriv E f + invDeriv E g := by
  rw [invDeriv, map_add, invCoeff_add]; rfl

theorem invDeriv_mul (f g : E.toAffine.FunctionField) :
    invDeriv E (f * g) = f * invDeriv E g + g * invDeriv E f := by
  rw [invDeriv, Derivation.leibniz, invCoeff_add, invCoeff_smul_mul, invCoeff_smul_mul]; rfl

theorem invDeriv_algebraMap (c : F) : invDeriv E (algebraMap F _ c) = 0 := by
  rw [invDeriv, D_coeff, invCoeff_zero]

theorem invDeriv_genX : invDeriv E (genX E) = 2 * genY E +
    algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃ := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).1

theorem invDeriv_genY : invDeriv E (genY E) = 3 * genX E ^ 2 +
    2 * algebraMap F _ E.a₂ * genX E + algebraMap F _ E.a₄ - algebraMap F _ E.a₁ * genY E := by
  apply invCoeff_eq
  exact (omegaAt_some_spec E _).2

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]

theorem isogCoeff_mul (φ : Isogeny E E') {x y : E.toAffine.FunctionField}
    {h : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y}
    (hφ : φ.1 = Point.some x y h) :
    isogCoeff φ * (2 * y + algebraMap F _ E'.a₁ * x + algebraMap F _ E'.a₃) = invDeriv E x := by
  have e := (omegaAt_some_spec E' h).1
  rw [← hφ, ← isogenyPullback_invariantDifferential, isogenyPullback_invariantDifferential_eq_smul,
    smul_smul] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at e
  rw [invDeriv, invCoeff_eq E e]
  ring

end Delta

section Dual

open TrivSqZeroExt

def dualMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    TrivSqZeroExt R R →+* TrivSqZeroExt S S where
  toFun z := inl (f z.fst) + inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem dualMap_fst {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).fst = f z.fst := by simp [dualMap]

theorem dualMap_snd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : TrivSqZeroExt R R) : (dualMap f z).snd = f z.snd := by simp [dualMap]

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

def invDerivHom : E.toAffine.FunctionField →+*
    TrivSqZeroExt E.toAffine.FunctionField E.toAffine.FunctionField where
  toFun f := inl f + inr (invDeriv E f)
  map_one' := by
    have h1 : invDeriv E 1 = 0 := by
      rw [← map_one (algebraMap F E.toAffine.FunctionField), invDeriv_algebraMap]
    ext <;> simp [h1]
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, MulOpposite.smul_eq_mul_unop, invDeriv_mul]
    ring
  map_zero' := by
    have h0 : invDeriv E 0 = 0 := by
      simpa using invDeriv_algebraMap E 0
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [invDeriv_add]

theorem invDerivHom_fst (f : E.toAffine.FunctionField) : (invDerivHom E f).fst = f := by
  simp [invDerivHom]

theorem invDerivHom_snd (f : E.toAffine.FunctionField) :
    (invDerivHom E f).snd = invDeriv E f := by
  simp [invDerivHom]

end Dual

section Gauss

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

def gaussDX : gaussRing W :=
  2 * gaussY W + algebraMap 𝒪 _ W.a₁ * gaussX W + algebraMap 𝒪 _ W.a₃

def gaussDY : gaussRing W :=
  3 * gaussX W ^ 2 + 2 * algebraMap 𝒪 _ W.a₂ * gaussX W + algebraMap 𝒪 _ W.a₄ -
    algebraMap 𝒪 _ W.a₁ * gaussY W

theorem gauss_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation (gaussX W) (gaussY W) := by
  have h := equation_gen (W.baseChange K)
  rw [← algebraMap_gaussX W K, ← algebraMap_gaussY W K] at h
  have e : (W.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField =
      (W.map (algebraMap 𝒪 (gaussRing W))).map (algebraMap (gaussRing W) _) :=
    (gaussCurve_map_functionField K W W).symm
  rw [e] at h
  exact (WeierstrassCurve.Affine.map_equation (W.map (algebraMap 𝒪 (gaussRing W))).toAffine
    (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) _ _).mp h

theorem gauss_dual_equation (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] :
    (W.map ((inlHom (gaussRing W) (gaussRing W)).comp (algebraMap 𝒪 (gaussRing W)))).toAffine.Equation
      (inl (gaussX W) + inr (gaussDX W)) (inl (gaussY W) + inr (gaussDY W)) := by
  have e := (WeierstrassCurve.Affine.equation_iff _ _).1 (gauss_equation W K)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, RingHom.comp_apply, inlHom_apply]
  ext
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, add_zero]
    linear_combination e
  · simp only [fst_add, fst_mul, fst_pow, fst_inl, fst_inr, snd_add, snd_mul, snd_pow, snd_inl,
      snd_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      nsmul_eq_mul, Nat.cast_ofNat, Nat.pred_eq_sub_one, mul_zero, zero_mul]
    simp only [gaussDX, gaussDY]
    norm_num
    ring

end Gauss

section GaussDeriv

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

def gaussDualA : W.toAffine.CoordinateRing →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  AdjoinRoot.lift (eval₂RingHom ((inlHom (gaussRing W) (gaussRing W)).comp
      (algebraMap 𝒪 (gaussRing W))) (inl (gaussX W) + inr (gaussDX W)))
    (inl (gaussY W) + inr (gaussDY W))
    (eval₂_polynomial_of_equation W _ (gauss_dual_equation W K))

theorem gaussDualA_algebraMap (c : 𝒪) :
    gaussDualA K W (algebraMap 𝒪 _ c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_X :
    gaussDualA K W (CoordinateRing.mk W (C X)) = inl (gaussX W) + inr (gaussDX W) := by
  rw [AdjoinRoot.mk_C, gaussDualA, AdjoinRoot.lift_of]
  simp

theorem gaussDualA_Y :
    gaussDualA K W (CoordinateRing.mk W Y) = inl (gaussY W) + inr (gaussDY W) := by
  rw [AdjoinRoot.mk_X, gaussDualA, AdjoinRoot.lift_root]

theorem fst_gaussDualA (a : W.toAffine.CoordinateRing) :
    (gaussDualA K W a).fst = algebraMap _ (gaussRing W) a := by
  have : ((fstHom 𝒪 (gaussRing W) (gaussRing W)).toRingHom).comp (gaussDualA K W) =
      algebraMap _ (gaussRing W) := by
    apply coordinateRing_ringHom_ext
    · intro c
      simp [gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]
    · show (gaussDualA K W (CoordinateRing.mk W (C X))).fst = _
      rw [gaussDualA_X, fst_add, fst_inl, fst_inr, add_zero]; rfl
    · show (gaussDualA K W (CoordinateRing.mk W Y)).fst = _
      rw [gaussDualA_Y, fst_add, fst_inl, fst_inr, add_zero]; rfl
  exact congrArg (fun f => f a) this

def gaussDual : gaussRing W →+* TrivSqZeroExt (gaussRing W) (gaussRing W) :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W) (g := gaussDualA K W)
    fun s => isUnit_iff_isUnit_fst.2 (by
      rw [fst_gaussDualA]; exact IsLocalization.map_units (gaussRing W) s)

theorem gaussDual_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussDual K W (algebraMap _ _ a) = gaussDualA K W a :=
  IsLocalization.lift_eq _ _

theorem gaussDual_algebraMap_base (c : 𝒪) :
    gaussDual K W (algebraMap 𝒪 (gaussRing W) c) = inl (algebraMap 𝒪 (gaussRing W) c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussDual_algebraMap, gaussDualA_algebraMap, ← IsScalarTower.algebraMap_apply]

def gaussDeriv (g : gaussRing W) : gaussRing W := (gaussDual K W g).snd

end GaussDeriv

section Compat

open TrivSqZeroExt

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [W.IsElliptic]

theorem algebraMap_gauss_const (c : 𝒪) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 _ c) =
      algebraMap K _ (algebraMap 𝒪 K c) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply 𝒪 K]

theorem algebraMap_gaussDeriv (g : gaussRing W) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussDeriv K W g) =
      invDeriv (W.baseChange K) (algebraMap (gaussRing W) _ g) := by
  have key : (dualMap (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField)).comp
      (gaussDual K W) = (invDerivHom (W.baseChange K)).comp (algebraMap (gaussRing W) _) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero, algebraMap_gauss_const,
          invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl, algebraMap_gaussX]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussX]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genX,
          gaussDX]
        simp only [map_add, map_mul, map_ofNat, algebraMap_gaussX, algebraMap_gaussY,
          algebraMap_gauss_const]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl, algebraMap_gaussY]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero, algebraMap_gaussY]
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, invDeriv_genY,
          gaussDY]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, algebraMap_gaussX,
          algebraMap_gaussY, algebraMap_gauss_const]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

theorem gaussResidue_gaussDeriv (g : gaussRing W) :
    gaussResidue W (residue _ (gaussDeriv K W g)) =
      invDeriv (W.map (residue 𝒪)) (gaussResidue W (residue _ g)) := by
  have key : (dualMap ((gaussResidue W).comp (residue (gaussRing W)))).comp (gaussDual K W) =
      (invDerivHom (W.map (residue 𝒪))).comp ((gaussResidue W).comp (residue (gaussRing W))) := by
    apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
    apply coordinateRing_ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
        gaussDual_algebraMap_base]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_inl]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_inl, map_zero,
          gaussResidue_residue_algebraMap, invDeriv_algebraMap]
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_X]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W (C X)) =
        gaussX W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussX, invDeriv_genX, gaussDX]
        simp only [map_add, map_mul, map_ofNat, RingHom.comp_apply, gaussResidue_gaussX,
          gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
    · simp only [RingHom.comp_apply, gaussDual_algebraMap, gaussDualA_Y]
      rw [show algebraMap W.toAffine.CoordinateRing (gaussRing W) (CoordinateRing.mk W Y) =
        gaussY W from rfl]
      ext
      · rw [dualMap_fst, invDerivHom_fst, fst_add, fst_inl, fst_inr, add_zero]; rfl
      · rw [dualMap_snd, invDerivHom_snd, snd_add, snd_inl, snd_inr, zero_add, gaussResidue_gaussY, invDeriv_genY, gaussDY]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, RingHom.comp_apply,
          gaussResidue_gaussX, gaussResidue_gaussY, gaussResidue_residue_algebraMap]
        rfl
  have := congrArg (fun f => (f g).snd) key
  simp only [RingHom.comp_apply, dualMap_snd, invDerivHom_snd] at this
  rw [gaussDeriv]
  exact this

end Compat

section Isog

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type u) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))

set_option maxHeartbeats 1000000 in

theorem exists_invConst_reduceIsogeny :
    ∃ c : 𝒪, algebraMap 𝒪 K c = invConst φ ∧
      residue 𝒪 c = invConst (reduceIsogeny K W W' φ) := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  set u : gaussRing W := 2 * y + algebraMap 𝒪 _ W'.a₁ * x + algebraMap 𝒪 _ W'.a₃ with hu_def

  have hu_res : gaussResidue W (residue _ u) = 2 * gaussResidue W (residue _ y) +
      algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₁ * gaussResidue W (residue _ x) +
        algebraMap (ResidueField 𝒪) _ (W'.map (residue 𝒪)).a₃ := by
    simp only [hu_def, map_add, map_mul, map_ofNat, gaussResidue_residue_algebraMap]
    rfl
  have hu_ne : gaussResidue W (residue _ u) ≠ 0 := by
    have hg := (reduceIsogeny K W W' φ).isGenPt
    rw [hφ'] at hg
    have hd := genDen_ne_zero (W'.map (residue 𝒪))
    intro h0
    apply hd
    apply (genEval (W'.map (residue 𝒪)) _ hg).toRingHom.injective
    rw [map_zero, ← h0, hu_res]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_ofNat,
      AlgHom.commutes, genEval_genX, genEval_genY]
    rfl
  have hu : IsUnit u := by
    by_contra hnu
    exact hu_ne (by rw [(residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hnu), map_zero])

  have e1 : isogCoeff φ * algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u =
      algebraMap (gaussRing W) _ (gaussDeriv K W x) := by
    rw [algebraMap_gaussDeriv, ← isogCoeff_mul φ hφ]
    congr 1
    simp only [hu_def, map_add, map_mul, map_ofNat, algebraMap_gauss_const]
    rfl
  set v : gaussRing W := gaussDeriv K W x * ↑hu.unit⁻¹ with hv_def
  have hv : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField v = isogCoeff φ := by
    have hne : algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hu.ne_zero
    rw [hv_def, map_mul, ← e1, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

  have hint : invConst φ ∈ Set.range (algebraMap 𝒪 K) := by
    by_contra hX
    obtain ⟨t, ht, hte⟩ := exists_inv_mem_of_notMem_range K hX
    have hc0 : invConst φ ≠ 0 := fun h0 => hX ⟨0, by rw [map_zero, h0]⟩
    have h1 : v * algebraMap 𝒪 (gaussRing W) t = 1 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
      rw [map_mul, hv, algebraMap_gauss_const, hte, ← algebraMap_invConst, map_inv₀,
        mul_inv_cancel₀ ((_root_.map_ne_zero _).2 hc0), map_one]
    have : IsUnit (algebraMap 𝒪 (gaussRing W) t) :=
      isUnit_iff_exists_inv.2 ⟨v, by rw [mul_comm]; exact h1⟩
    exact (mem_maximalIdeal _).1 ht ((isUnit_map_iff (algebraMap 𝒪 (gaussRing W)) t).1 this)
  obtain ⟨c, hc⟩ := hint
  refine ⟨c, hc, ?_⟩
  have hvc : algebraMap 𝒪 (gaussRing W) c = v := by
    apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
    rw [algebraMap_gauss_const, hc, algebraMap_invConst, hv]

  have e2 := isogCoeff_mul (reduceIsogeny K W W' φ) hφ'
  rw [← gaussResidue_gaussDeriv K W x] at e2
  have e2' : isogCoeff (reduceIsogeny K W W' φ) = gaussResidue W (residue _ v) := by
    have hres_u : gaussResidue W (residue _ u) * gaussResidue W (residue _ ↑hu.unit⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, IsUnit.mul_val_inv, map_one, map_one]
    rw [hv_def, map_mul, map_mul, ← e2, ← hu_res, mul_assoc, hres_u, mul_one]
  apply (algebraMap (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.FunctionField).injective
  rw [algebraMap_invConst, e2', ← hvc, gaussResidue_residue_algebraMap]

end Isog

end

end GroundTheory.Global
