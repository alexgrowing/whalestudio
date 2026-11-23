import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionRespectsAdd

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

theorem redU_apply (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (P : ((V.baseChange K).baseChange (liftField K W)).toAffine.Point) :
    redU K W V P = reducePoint (liftField K W) (V.map (liftJ W))
      (pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
        (liftJ_algebraMap K W)) P) := by
  simp only [redU, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    reductionHom_apply]

theorem pushPt_apply (V : WeierstrassCurve 𝒪)
    (P : ((V.map (liftJ W)).map (residue (gaussRing (gaussCurve W W)))).toAffine.Point) :
    pushPt W V P = pointCongr (pushCurve_eq W V) (pointMapRing (pushField W) _ P) := by
  simp only [pushPt, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]

variable [W.IsElliptic]

theorem exists_integral_of_reducePoint_ne_zero {𝒪₀ : Type*} [CommRing 𝒪₀] [IsDomain 𝒪₀]
    [IsDiscreteValuationRing 𝒪₀] (K₀ : Type*) [Field K₀] [Algebra 𝒪₀ K₀] [IsFractionRing 𝒪₀ K₀]
    (V : WeierstrassCurve 𝒪₀) {P : (curveK K₀ V).Point} (hP : reducePoint K₀ V P ≠ 0) :
    ∃ (x y : 𝒪₀) (h : (curveK K₀ V).Nonsingular (algebraMap 𝒪₀ K₀ x) (algebraMap 𝒪₀ K₀ y)),
      P = Point.some _ _ h := by
  rcases point_cases K₀ V P with h0 | ⟨X₀, Y₀, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · exact absurd (by rw [h0, reducePoint_zero]) hP
  · exact absurd (reducePoint_some_notMem K₀ V h hX) hP
  · exact ⟨x, y, h, rfl⟩

theorem liftPt₁₂_eq : ∃ (x y : gaussRing (gaussCurve W W)) (h : _),
    liftPt₁ K W + liftPt₂ K W = Point.some (algebraMap _ (liftField K W) x)
      (algebraMap _ (liftField K W) y) h := by
  have hsum : pushPt W W (redU K W W (liftPt₁ K W + liftPt₂ K W)) =
      univPt₁ (W.map (residue 𝒪)) + univPt₂ (W.map (residue 𝒪)) := by
    rw [map_add, map_add, pushPt_redU_liftPt₁, pushPt_redU_liftPt₂]
  have hne : redU K W W (liftPt₁ K W + liftPt₂ K W) ≠ 0 := fun h0 =>
    isGenPt_ne_zero _ (isGenPt_univPt₁₂ (W.map (residue 𝒪))) (by rw [← hsum, h0, map_zero])
  rw [redU_apply] at hne
  obtain ⟨x, y, h, hP⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have hP' : liftPt₁ K W + liftPt₂ K W = pointCongr (map_baseChange_eq_map_of K W (liftJ W)
      (liftField K W) (liftJ_algebraMap K W)).symm (Point.some _ _ h) := by
    rw [← hP, pointCongr_pointCongr]; rfl
  rw [hP', pointCongr_some]
  exact ⟨x, y, _, rfl⟩

omit [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))] [W.IsElliptic] in
theorem pointCongr_pointCongr_eq {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (h₃ : V₁ = V₃)
    (P : V₁.toAffine.Point) : pointCongr h₂ (pointCongr h₁ P) = pointCongr h₃ P := by
  subst h₁; subst h₂; rfl

variable (W' : WeierstrassCurve 𝒪) [W'.IsElliptic]

theorem pushField_comp_fieldEvalRed {x y : gaussRing (gaussCurve W W)}
    (hxy : (W.map (liftJ W)).toAffine.Equation x y)
    (hx : Function.Injective (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x)))
    {R : ((W.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point}
    (hR : IsGenPt (W.map (residue 𝒪)) R) (hRx : xOf _ R = pushField W (residue _ x))
    (hRy : yOf _ R = pushField W (residue _ y)) :
    (pushField W).comp (fieldEvalRed W (liftJ W) hxy hx) =
      (genEval (W.map (residue 𝒪)) R hR).toRingHom := by
  apply ringHom_ext_functionField
  · intro c
    rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
      pushField_comp_residueField_map]
    exact ((genEval _ R hR).commutes c).symm
  · rw [RingHom.comp_apply, fieldEvalRed_genX, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      genEval_genX, hRx]
  · rw [RingHom.comp_apply, fieldEvalRed_genY, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      genEval_genY, hRy]

set_option maxHeartbeats 1000000 in

theorem pushPt_redU_genEval {x y : gaussRing (gaussCurve W W)}
    (h : ((W.baseChange K).baseChange (liftField K W)).toAffine.Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y))
    (hg : IsGenPt (W.baseChange K) (Point.some _ _ h))
    {R : ((W.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point}
    (hR : IsGenPt (W.map (residue 𝒪)) R)
    (hpush : pushPt W W (redU K W W (Point.some _ _ h)) = R)
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    pushPt W W' (redU K W W' (Point.map (genEval (W.baseChange K) _ hg) Q)) =
      Point.map (genEval (W.map (residue 𝒪)) R hR) (reduceFF K W W' Q) := by
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e'] at hpush
  subst hpush
  have hxy : (W.map (liftJ W)).toAffine.Equation x y := by
    have h₁ : ((W.map (liftJ W)).map (algebraMap _ (liftField K W))).toAffine.Equation
        (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y) := by
      rw [← map_baseChange_eq_map_of K W (liftJ W) (liftField K W) (liftJ_algebraMap K W)]
      exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W.map (liftJ W)).toAffine
      (IsFractionRing.injective _ (liftField K W)) x y).mp h₁
  have hx : Function.Injective (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (pushField W (residue _ x)) := hR
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (pushField W (residue _ x)) p =
        pushField W (eval₂RingHom (ResidueField.map (liftJ W)) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, pushField_comp_residueField_map]
    rw [key, hp, map_zero]
  have main := reducePoint_genEval (K := K) (W := W) (W' := W') (j := liftJ W)
    (M := liftField K W) (hxy := hxy) (hx := hx) (liftJ_algebraMap K W) h hg Q
  have hring := pushField_comp_fieldEvalRed W hxy hx hR rfl rfl
  rw [redU_apply, main, pushPt_apply, pointMapRing_pointCongr, pointCongr_pointCongr,
    pointMapRing_pointMapRing, pointMapRing_congr hring, map_eq_pointCongr_pointMapRing]
  exact pointCongr_pointCongr_eq _ _ _ _

set_option maxHeartbeats 1000000 in

theorem univAdd_reduceFF
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point)
    (hQ : RespectsAdd (W.baseChange K) (W'.baseChange K) Q) : UnivAdd (reduceFF K W W' Q) := by
  haveI : DecidableEq (ResidueField (gaussRing (gaussCurve W W))) := Classical.decEq _
  obtain ⟨h₁, e₁⟩ := liftPt₁_eq K W
  obtain ⟨h₂, e₂⟩ := liftPt₂_eq K W
  obtain ⟨x₃, y₃, h₃, e₃⟩ := liftPt₁₂_eq K W
  have g₁ : IsGenPt (W.baseChange K) (Point.some _ _ h₁) := by
    rw [← e₁]; exact isGenPt_liftPt₁ K W
  have g₂ : IsGenPt (W.baseChange K) (Point.some _ _ h₂) := by
    rw [← e₂]; exact isGenPt_liftPt₂ K W
  have g₃ : IsGenPt (W.baseChange K) (Point.some _ _ h₃) := by
    rw [← e₃]; exact isGenPt_liftPt₁₂ K W
  have hsum : pushPt W W (redU K W W (liftPt₁ K W + liftPt₂ K W)) =
      univPt₁ (W.map (residue 𝒪)) + univPt₂ (W.map (residue 𝒪)) := by
    rw [map_add, map_add, pushPt_redU_liftPt₁, pushPt_redU_liftPt₂]
  have k₁ := pushPt_redU_genEval K W W' h₁ g₁ (isGenPt_univPt₁ _)
    (by rw [← e₁]; exact pushPt_redU_liftPt₁ K W) Q
  have k₂ := pushPt_redU_genEval K W W' h₂ g₂ (isGenPt_univPt₂ _)
    (by rw [← e₂]; exact pushPt_redU_liftPt₂ K W) Q
  have k₃ := pushPt_redU_genEval K W W' h₃ g₃ (isGenPt_univPt₁₂ _)
    (by rw [← e₃]; exact hsum) Q
  have hs : Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some _ _ h₃ := by
    rw [← e₁, ← e₂, e₃]
  have hadd := (respectsAdd_iff Q).mp hQ (liftField K W) _ _ g₁ g₂ (hs ▸ g₃)
  rw [genEval_congr _ hs _ g₃] at hadd
  have := congrArg (fun P => pushPt W W' (redU K W W' P)) hadd
  simp only [map_add] at this
  rw [k₁, k₂, k₃] at this
  exact this

theorem respectsAdd_reduceFF
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point)
    (hQ : RespectsAdd (W.baseChange K) (W'.baseChange K) Q) :
    RespectsAdd (W.map (residue 𝒪)) (W'.map (residue 𝒪)) (reduceFF K W W' Q) :=
  respectsAdd_of_univAdd _ (univAdd_reduceFF K W W' Q hQ)

def reduceHom :
    isogHom (W.baseChange K) (W'.baseChange K) →+ isogHom (W.map (residue 𝒪)) (W'.map (residue 𝒪))
    where
  toFun Q := ⟨reduceFF K W W' Q.1, respectsAdd_reduceFF K W W' Q.1 Q.2⟩
  map_zero' := Subtype.ext (map_zero (reduceFF K W W'))
  map_add' Q R := Subtype.ext (map_add (reduceFF K W W') Q.1 R.1)

theorem reduceHom_val (Q : isogHom (W.baseChange K) (W'.baseChange K)) :
    (reduceHom K W W' Q).1 = reduceFF K W W' Q.1 :=
  rfl

end Main

end

end GroundTheory.Global
