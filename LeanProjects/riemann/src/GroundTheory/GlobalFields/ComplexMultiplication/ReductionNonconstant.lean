import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionComp
import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddGeneric
import GroundTheory.GlobalFields.ComplexMultiplication.DualDescent

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section Setup

abbrev liftField₂ : Type _ :=
  ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField).toAffine.FunctionField

abbrev liftJ₂ : 𝒪 →+* gaussRing (gaussCurve W W') :=
  (algebraMap (gaussRing W) (gaussRing (gaussCurve W W'))).comp (algebraMap 𝒪 (gaussRing W))

theorem liftJ₂_algebraMap (c : 𝒪) :
    algebraMap K (liftField₂ K W W') (algebraMap 𝒪 K c) =
      algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (liftJ₂ W W' c) := by
  rw [RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply (gaussRing W) (gaussRing (gaussCurve W W')) (liftField₂ K W W'),
    IsScalarTower.algebraMap_apply (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W'),
    ← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField₂ K W W')]

theorem baseChange_liftField₂_eq :
    ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField).baseChange
      (liftField₂ K W W') = (W'.baseChange K).baseChange (liftField₂ K W W') := by
  rw [baseChange_baseChange]
  show W'.map (((algebraMap (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')).comp
      (algebraMap (gaussRing W) _)).comp (algebraMap 𝒪 (gaussRing W))) =
    W'.map ((algebraMap K (liftField₂ K W W')).comp (algebraMap 𝒪 K))
  refine congrArg W'.map (RingHom.ext fun c => ?_)
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply 𝒪 (gaussRing W) (W.baseChange K).toAffine.FunctionField,
    IsScalarTower.algebraMap_apply 𝒪 K (W.baseChange K).toAffine.FunctionField,
    ← IsScalarTower.algebraMap_apply K _ (liftField₂ K W W')]

variable [W'.IsElliptic]

def genPt₂ : ((W'.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point :=
  pointCongr (baseChange_liftField₂_eq K W W')
    (GroundTheory.Arith.Abelian.genericPoint
      ((gaussCurve W W').baseChange (W.baseChange K).toAffine.FunctionField))

theorem genPt₂_eq : ∃ h, genPt₂ K W W' = Point.some
    (algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (gaussX (gaussCurve W W')))
    (algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W') (gaussY (gaussCurve W W'))) h := by
  rw [genPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact exists_some_eq _
    (algebraMap_gaussX (gaussCurve W W') (W.baseChange K).toAffine.FunctionField).symm
    (algebraMap_gaussY (gaussCurve W W') (W.baseChange K).toAffine.FunctionField).symm

theorem transOver_genPt₂ :
    TransOver (W'.baseChange K) (W.baseChange K).toAffine.FunctionField (genPt₂ K W W') := by
  rw [genPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

end Setup

section Red

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W')))]

def red₂ (V : WeierstrassCurve 𝒪)
    (P : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    ((V.map (liftJ₂ W W')).map (residue (gaussRing (gaussCurve W W')))).toAffine.Point :=
  reducePoint (liftField₂ K W W') (V.map (liftJ₂ W W'))
    (pointCongr (map_baseChange_eq_map_of K V (liftJ₂ W W') (liftField₂ K W W')
      (liftJ₂_algebraMap K W W')) P)

theorem red₂_add (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (P Q : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    red₂ K W W' V (P + Q) = red₂ K W W' V P + red₂ K W W' V Q := by
  rw [red₂, red₂, red₂, map_add, reducePoint_add]

theorem red₂_zero (V : WeierstrassCurve 𝒪) : red₂ K W W' V 0 = 0 := by
  rw [red₂, map_zero, reducePoint_zero]

variable [W.IsElliptic] [W'.IsElliptic]

theorem red₂_map_of_reduceFF_eq_zero
    {R : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hR : reduceFF K W W' R = 0) :
    red₂ K W W' W' (Point.map (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W')) R) = 0 := by
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have e := gaussCurve_map_functionField K W W'
  have h0 : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr e.symm R) = 0 := by
    have := hR
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      reductionHom_apply] at this
    rwa [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff] at this
  rcases point_cases (W.baseChange K).toAffine.FunctionField (gaussCurve W W') (pointCongr e.symm R)
    with hz | ⟨X₀, Y₀, h, hP, hX⟩ | ⟨x, y, h, hP⟩
  · rw [pointCongr_eq_zero_iff] at hz
    rw [hz, map_zero, red₂_zero]
  · have hRe : R = pointCongr e (Point.some _ _ h) := by
      rw [← hP, pointCongr_pointCongr]; rfl
    rw [pointCongr_some] at hRe
    subst hRe
    have hσ : (algebraMap (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')).comp
        (algebraMap (gaussRing W) _) = (algebraMap (gaussRing (gaussCurve W W'))
          (liftField₂ K W W')).comp (algebraMap (gaussRing W) _) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have hX' := map_notMem_range (W.baseChange K).toAffine.FunctionField (liftField₂ K W W') hσ hX
    rw [red₂, Point.map_some, pointCongr_some]
    exact reducePoint_some_notMem _ _ _ hX'
  · exfalso
    have n := nonsingular_residue_of_isElliptic _ _ h.1
    rw [hP, reducePoint_some_integral _ _ h n] at h0
    exact Point.some_ne_zero n h0

end Red

end

end GroundTheory.Global
