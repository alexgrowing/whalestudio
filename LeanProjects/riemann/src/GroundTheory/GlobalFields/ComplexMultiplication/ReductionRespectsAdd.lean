import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionEval
import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChange

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

section Push

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)

def pushField : ResidueField (gaussRing (gaussCurve W W)) →+* univField (W.map (residue 𝒪)) :=
  (ffCongr (gaussCurve_map_residue W W)).toRingHom.comp
    ((ffMap (gaussResidue W) ((gaussCurve W W).map (residue (gaussRing W)))).comp
      (gaussResidue (gaussCurve W W)))

theorem pushField_residue_algebraMap (g : gaussRing W) :
    pushField W (residue _ (algebraMap (gaussRing W) (gaussRing (gaussCurve W W)) g)) =
      algebraMap (W.map (residue 𝒪)).toAffine.FunctionField _ (gaussResidue W (residue _ g)) := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_residue_algebraMap,
    ffMap_algebraMap]
  exact ffCongr_algebraMap _ _

theorem pushField_gaussX :
    pushField W (residue _ (gaussX (gaussCurve W W))) = genX _ := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_gaussX, ffMap_genX]
  exact ffCongr_genX _

theorem pushField_gaussY :
    pushField W (residue _ (gaussY (gaussCurve W W))) = genY _ := by
  rw [pushField, RingHom.comp_apply, RingHom.comp_apply, gaussResidue_gaussY, ffMap_genY]
  exact ffCongr_genY _

end Push

section Main

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

abbrev liftField : Type _ :=
  ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.FunctionField

abbrev liftJ : 𝒪 →+* gaussRing (gaussCurve W W) :=
  (algebraMap (gaussRing W) (gaussRing (gaussCurve W W))).comp (algebraMap 𝒪 (gaussRing W))

theorem liftJ_algebraMap (c : 𝒪) :
    algebraMap K (liftField K W) (algebraMap 𝒪 K c) =
      algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (liftJ W c) := by
  rw [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply (gaussRing W) (gaussRing (gaussCurve W W)) (liftField K W),
    IsScalarTower.algebraMap_apply (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (liftField K W),
    ← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField K W)]

theorem pushField_comp_residueField_map :
    (pushField W).comp (ResidueField.map (liftJ W)) =
      algebraMap (ResidueField 𝒪) (univField (W.map (residue 𝒪))) := by
  refine RingHom.ext fun c => ?_
  obtain ⟨c, rfl⟩ := residue_surjective c
  rw [RingHom.comp_apply, ResidueField.map_residue, RingHom.comp_apply,
    pushField_residue_algebraMap, gaussResidue_residue_algebraMap,
    ← IsScalarTower.algebraMap_apply]

theorem pushCurve_eq (V : WeierstrassCurve 𝒪) :
    ((V.map (liftJ W)).map (residue _)).map (pushField W) =
      (V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪))) := by
  show V.map (((pushField W).comp (residue _)).comp (liftJ W)) =
    V.map ((algebraMap (ResidueField 𝒪) _).comp (residue 𝒪))
  have h : ((pushField W).comp (residue _)).comp (liftJ W) =
      (algebraMap (ResidueField 𝒪) (univField (W.map (residue 𝒪)))).comp (residue 𝒪) := by
    rw [← pushField_comp_residueField_map, RingHom.comp_assoc, RingHom.comp_assoc,
      ResidueField.map_comp_residue]
  rw [h]

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

def pushPt (V : WeierstrassCurve 𝒪) :
    ((V.map (liftJ W)).map (residue _)).toAffine.Point →+
      ((V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Point :=
  (pointCongr (pushCurve_eq W V)).toAddMonoidHom.comp (pointMapRing (pushField W) _)

def redU (V : WeierstrassCurve 𝒪) [V.IsElliptic] :
    ((V.baseChange K).baseChange (liftField K W)).toAffine.Point →+
      ((V.map (liftJ W)).map (residue _)).toAffine.Point :=
  (reductionHom (liftField K W) (V.map (liftJ W))).comp
    (pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
      (liftJ_algebraMap K W))).toAddMonoidHom

theorem pushPt_redU_some (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    {x y : gaussRing (gaussCurve W W)}
    (h : ((V.baseChange K).baseChange (liftField K W)).toAffine.Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y)) :
    ∃ h' : ((V.map (residue 𝒪)).baseChange (univField (W.map (residue 𝒪)))).toAffine.Nonsingular
        (pushField W (residue _ x)) (pushField W (residue _ y)),
      pushPt W V (redU K W V (.some _ _ h)) = .some _ _ h' := by
  have h₁ : (curveK (liftField K W) (V.map (liftJ W))).Nonsingular
      (algebraMap _ (liftField K W) x) (algebraMap _ (liftField K W) y) := by
    show ((V.map (liftJ W)).map (algebraMap _ (liftField K W))).toAffine.Nonsingular _ _
    rw [← map_baseChange_eq_map_of K V (liftJ W) (liftField K W) (liftJ_algebraMap K W)]
    exact h
  have n := nonsingular_residue_of_isElliptic (liftField K W) (V.map (liftJ W)) h₁.1
  obtain ⟨h', e⟩ := pointMapRing_some (pushField W) ((V.map (liftJ W)).map (residue _)) n
  refine ⟨by rw [← pushCurve_eq W V]; exact h', ?_⟩
  have e₁ : pointCongr (map_baseChange_eq_map_of K V (liftJ W) (liftField K W)
      (liftJ_algebraMap K W)) (Point.some _ _ h) = Point.some _ _ h₁ := pointCongr_some _ h
  have e₂ : redU K W V (.some _ _ h) = .some _ _ n := by
    show reducePoint (liftField K W) (V.map (liftJ W)) (pointCongr _ (.some _ _ h)) = _
    rw [e₁, reducePoint_some_integral _ _ h₁ n]
  rw [e₂]
  exact (congrArg (pointCongr (pushCurve_eq W V)) e).trans (pointCongr_some _ _)

instance isElliptic_baseChange_ring {R : Type*} [CommRing R] (V : WeierstrassCurve R) [V.IsElliptic]
    (A : Type*) [CommRing A] [Algebra R A] : (V.baseChange A).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

variable [W.IsElliptic]

def liftPt₁ : ((W.baseChange K).baseChange (liftField K W)).toAffine.Point :=
  Point.map (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField (liftField K W))
    (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))

theorem baseChange_liftField_eq :
    ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField).baseChange
      (liftField K W) = (W.baseChange K).baseChange (liftField K W) := by
  show W.map (((algebraMap (W.baseChange K).toAffine.FunctionField (liftField K W)).comp
      (algebraMap (gaussRing W) _)).comp (algebraMap 𝒪 (gaussRing W))) =
    W.map ((algebraMap K (liftField K W)).comp (algebraMap 𝒪 K))
  refine congrArg W.map (RingHom.ext fun c => ?_)
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField K W)]

def liftPt₂ : ((W.baseChange K).baseChange (liftField K W)).toAffine.Point :=
  pointCongr (baseChange_liftField_eq K W)
    (GroundTheory.Arith.Abelian.genericPoint
      ((gaussCurve W W).baseChange (W.baseChange K).toAffine.FunctionField))

theorem exists_some_eq {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}
    {a b a' b' : F} (h : V.toAffine.Nonsingular a b) (ha : a = a') (hb : b = b') :
    ∃ h', (Point.some a b h : V.toAffine.Point) = Point.some a' b' h' := by
  subst ha; subst hb; exact ⟨h, rfl⟩

theorem liftPt₁_eq : ∃ h, liftPt₁ K W = Point.some
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussX W)))
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussY W))) h := by
  have hx : algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussX W)) =
        algebraMap (W.baseChange K).toAffine.FunctionField _ (genX (W.baseChange K)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (gaussRing W)
      (W.baseChange K).toAffine.FunctionField (liftField K W), algebraMap_gaussX]
  have hy : algebraMap (gaussRing (gaussCurve W W)) (liftField K W)
      (algebraMap (gaussRing W) _ (gaussY W)) =
        algebraMap (W.baseChange K).toAffine.FunctionField _ (genY (W.baseChange K)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (gaussRing W)
      (W.baseChange K).toAffine.FunctionField (liftField K W), algebraMap_gaussY]
  rw [liftPt₁, GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
  exact exists_some_eq _ hx.symm hy.symm

theorem liftPt₂_eq : ∃ h, liftPt₂ K W = Point.some
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (gaussX (gaussCurve W W)))
    (algebraMap (gaussRing (gaussCurve W W)) (liftField K W) (gaussY (gaussCurve W W))) h := by
  rw [liftPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact exists_some_eq _
    (algebraMap_gaussX (gaussCurve W W) (W.baseChange K).toAffine.FunctionField).symm
    (algebraMap_gaussY (gaussCurve W W) (W.baseChange K).toAffine.FunctionField).symm

theorem pushPt_redU_liftPt₁ :
    pushPt W W (redU K W W (liftPt₁ K W)) = univPt₁ (W.map (residue 𝒪)) := by
  obtain ⟨h, e⟩ := liftPt₁_eq K W
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e, e', univPt₁, GroundTheory.Arith.Abelian.genericPoint, Point.map_some, Point.some.injEq]
  constructor
  · rw [pushField_residue_algebraMap, gaussResidue_gaussX]; rfl
  · rw [pushField_residue_algebraMap, gaussResidue_gaussY]; rfl

theorem pushPt_redU_liftPt₂ :
    pushPt W W (redU K W W (liftPt₂ K W)) = univPt₂ (W.map (residue 𝒪)) := by
  obtain ⟨h, e⟩ := liftPt₂_eq K W
  obtain ⟨h', e'⟩ := pushPt_redU_some K W W h
  rw [e, e', univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.some.injEq]
  exact ⟨pushField_gaussX W, pushField_gaussY W⟩

theorem isGenPt_liftPt₁ : IsGenPt (W.baseChange K) (liftPt₁ K W) :=
  isGenPt_map _ _ (transcendental_genX _)

theorem transOver_liftPt₂ :
    TransOver (W.baseChange K) (W.baseChange K).toAffine.FunctionField (liftPt₂ K W) := by
  rw [liftPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

theorem isGenPt_liftPt₂ : IsGenPt (W.baseChange K) (liftPt₂ K W) := (transOver_liftPt₂ K W).isGenPt

theorem isGenPt_liftPt₁₂ : IsGenPt (W.baseChange K) (liftPt₁ K W + liftPt₂ K W) :=
  ((transOver_liftPt₂ K W).add_left (GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))).isGenPt

end Main

end

end GroundTheory.Global
