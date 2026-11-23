import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionGauss

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
include hxy in
theorem eval₂_polynomial_of_equation :
    W.toAffine.polynomial.eval₂ (eval₂RingHom j x) y = 0 := by
  have e := (equation_iff _ _).mp hxy
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom]
  linear_combination e

def coordEval : W.toAffine.CoordinateRing →+* Λ :=
  AdjoinRoot.lift (eval₂RingHom j x) y (eval₂_polynomial_of_equation W j hxy)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
theorem coordEval_mk (p : 𝒪[X][Y]) :
    coordEval W j hxy (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom j x) y :=
  AdjoinRoot.lift_mk _ _

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j] in
theorem coordEval_algebraMap (c : 𝒪) :
    coordEval W j hxy (algebraMap 𝒪 W.toAffine.CoordinateRing c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    coordEval, AdjoinRoot.lift_of]
  simp

include hxy in

theorem equation_residue_of_equation :
    ((W.map (residue 𝒪)).map (ResidueField.map j)).toAffine.Equation (residue Λ x)
      (residue Λ y) := by
  have e := (equation_iff _ _).mp hxy
  rw [equation_iff]
  have := congrArg (residue Λ) e
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_mul, map_pow] at this ⊢
  simp only [← RingHom.comp_apply (ResidueField.map j), ResidueField.map_comp_residue]
  simpa only [RingHom.comp_apply] using this

include hxy in

def coordEvalRed :
    (W.map (residue 𝒪)).toAffine.CoordinateRing →+* ResidueField Λ :=
  AdjoinRoot.lift (eval₂RingHom (ResidueField.map j) (residue Λ x)) (residue Λ y)
    (eval₂_polynomial_of_equation (W.map (residue 𝒪)) (ResidueField.map j)
      (equation_residue_of_equation W j hxy))

theorem coordReduce_of (q : 𝒪[X]) :
    coordReduce W (AdjoinRoot.of _ q) = AdjoinRoot.of _ (q.map (residue 𝒪)) := by
  rw [← AdjoinRoot.mk_C, coordReduce, CoordinateRing.map_mk, Polynomial.map_C, ← AdjoinRoot.mk_C]
  rfl

theorem coordReduce_root :
    coordReduce W (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root (W.map (residue 𝒪)).toAffine.polynomial := by
  rw [← AdjoinRoot.mk_X, coordReduce, CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]

theorem residue_coordEval (a : W.toAffine.CoordinateRing) :
    residue Λ (coordEval W j hxy a) = coordEvalRed W j hxy (coordReduce W a) := by
  have : (residue Λ).comp (coordEval W j hxy) = (coordEvalRed W j hxy).comp (coordReduce W) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_C, coe_eval₂RingHom, eval₂_C, ResidueField.map_residue]
      · simp only [RingHom.comp_apply, coordReduce_of, coordEval, coordEvalRed, AdjoinRoot.lift_of,
          Polynomial.map_X, coe_eval₂RingHom, eval₂_X]
    · simp only [RingHom.comp_apply, coordReduce_root, coordEval, coordEvalRed,
        AdjoinRoot.lift_root]
  exact congrArg (· a) this

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

theorem coordinateRing_ringHom_ext {S : Type*} [CommRing S]
    {f g : W.toAffine.CoordinateRing →+* S}
    (h₁ : ∀ c : 𝒪, f (algebraMap 𝒪 _ c) = g (algebraMap 𝒪 _ c))
    (h₂ : f (CoordinateRing.mk W (C X)) = g (CoordinateRing.mk W (C X)))
    (h₃ : f (CoordinateRing.mk W Y) = g (CoordinateRing.mk W Y)) : f = g := by
  have hc : ∀ c : 𝒪, algebraMap 𝒪 W.toAffine.CoordinateRing c =
      AdjoinRoot.of W.toAffine.polynomial (C c) := fun c => by
    rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, hc] using h₁ c
    · simpa only [RingHom.comp_apply, AdjoinRoot.mk_C] using h₂
  · simpa only [AdjoinRoot.mk_X] using h₃

variable (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

include hx in

theorem coordEvalRed_injective : Function.Injective (coordEvalRed W j hxy) := by
  letI : Algebra (ResidueField 𝒪) (ResidueField Λ) := (ResidueField.map j).toAlgebra
  have h : ((W.map (residue 𝒪)).baseChange (ResidueField Λ)).toAffine.Equation (residue Λ x)
      (residue Λ y) := equation_residue_of_equation W j hxy
  have ht : Transcendental (ResidueField 𝒪) (residue Λ x) := transcendental_iff_injective.mpr hx
  exact evalAt_injective (W.map (residue 𝒪)) h ht

include hx in
theorem isUnit_coordEval (s : (gaussPrime W).primeCompl) : IsUnit (coordEval W j hxy s) := by
  by_contra hs
  have h0 : residue Λ (coordEval W j hxy s) = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hs)
  rw [residue_coordEval] at h0
  exact s.2 (RingHom.mem_ker.2 ((map_eq_zero_iff _ (coordEvalRed_injective W j hxy hx)).1 h0))

def gaussLift : gaussRing W →+* Λ :=
  IsLocalization.lift (M := (gaussPrime W).primeCompl) (S := gaussRing W)
    (isUnit_coordEval W j hxy hx)

theorem gaussLift_algebraMap (a : W.toAffine.CoordinateRing) :
    gaussLift W j hxy hx (algebraMap _ _ a) = coordEval W j hxy a :=
  IsLocalization.lift_eq _ _

theorem gaussLift_algebraMap_base (c : 𝒪) :
    gaussLift W j hxy hx (algebraMap 𝒪 (gaussRing W) c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussLift_algebraMap, coordEval_algebraMap]

instance isLocalHom_gaussLift : IsLocalHom (gaussLift W j hxy hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussPrime W).primeCompl a
  dsimp only at ha ⊢
  have hspec := IsLocalization.mk'_spec (gaussRing W) r s
  have hr : IsUnit (coordEval W j hxy r) := by
    have := congrArg (gaussLift W j hxy hx) hspec
    rw [map_mul, gaussLift_algebraMap, gaussLift_algebraMap] at this
    rw [← this]
    exact ha.mul (isUnit_coordEval W j hxy hx s)
  have hr' : r ∈ (gaussPrime W).primeCompl := by
    intro hP
    have h0 : coordReduce W r = 0 := hP
    have h1 : residue Λ (coordEval W j hxy r) = 0 := by rw [residue_coordEval, h0, map_zero]
    exact (residue_ne_zero_iff_isUnit _).2 hr h1
  have hu : IsUnit (IsLocalization.mk' (gaussRing W) r s *
      algebraMap W.toAffine.CoordinateRing (gaussRing W) (s : W.toAffine.CoordinateRing)) := by
    rw [hspec]; exact IsLocalization.map_units _ ⟨r, hr'⟩
  exact isUnit_of_mul_isUnit_left hu

def fieldEvalRed : (W.map (residue 𝒪)).toAffine.FunctionField →+* ResidueField Λ :=
  IsFractionRing.lift (coordEvalRed_injective W j hxy hx)

theorem residueField_map_gaussLift :
    ResidueField.map (gaussLift W j hxy hx) = (fieldEvalRed W j hxy hx).comp (gaussResidue W) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (W.toAffine.CoordinateRing ⧸ gaussPrime W))
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk]
  have e : algebraMap W.toAffine.CoordinateRing (gaussPrime W).ResidueField a =
      residue (gaussRing W) (algebraMap _ (gaussRing W) a) := by
    rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime (gaussPrime W))
      (gaussPrime W).ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
  rw [e, ResidueField.map_residue, gaussLift_algebraMap, gaussResidue_residue, fieldEvalRed,
    IsFractionRing.lift_algebraMap, residue_coordEval]

theorem fieldEvalRed_genX : fieldEvalRed W j hxy hx (genX (W.map (residue 𝒪))) = residue Λ x := by
  rw [genX, fieldEvalRed, IsFractionRing.lift_algebraMap, coordEvalRed, AdjoinRoot.lift_mk]
  simp

theorem fieldEvalRed_genY : fieldEvalRed W j hxy hx (genY (W.map (residue 𝒪))) = residue Λ y := by
  rw [genY, fieldEvalRed, IsFractionRing.lift_algebraMap, coordEvalRed, AdjoinRoot.lift_mk]
  simp

theorem fieldEvalRed_algebraMap (c : ResidueField 𝒪) :
    fieldEvalRed W j hxy hx (algebraMap (ResidueField 𝒪) _ c) = ResidueField.map j c := by
  rw [IsScalarTower.algebraMap_apply (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.CoordinateRing,
    fieldEvalRed, IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply (ResidueField 𝒪)
      (ResidueField 𝒪)[X], AdjoinRoot.algebraMap_eq, coordEvalRed, AdjoinRoot.lift_of]
  simp

section Fraction

variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (M : Type*) [Field M]
  [Algebra Λ M]

theorem comp_algebraMap_gaussLift (σ : (W.baseChange K).toAffine.FunctionField →+* M)
    (hσ : ∀ c : 𝒪, σ (algebraMap 𝒪 _ c) = algebraMap Λ M (j c))
    (hX : σ (genX (W.baseChange K)) = algebraMap Λ M x)
    (hY : σ (genY (W.baseChange K)) = algebraMap Λ M y) :
    σ.comp (algebraMap (gaussRing W) _) = (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
  apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
  apply coordinateRing_ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, gaussLift_algebraMap,
      coordEval_algebraMap, hσ, gaussLift_algebraMap_base]
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussX, algebraMap_gaussX, hX]
    simp
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussY, algebraMap_gaussY, hY]
    simp

end Fraction

end

end GroundTheory.Global
