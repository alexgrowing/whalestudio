import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionPoints
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionGauss
import GroundTheory.ArithmeticGeometry.AbelianVarieties.ReductionTorsion

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian WeierstrassCurve.Affine

section PointMap

variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L] (f : F →+* L)
  (V : WeierstrassCurve F)

def pointMapRing : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI := f.toAlgebra
  Point.map (W' := V) (Algebra.ofId F L)

theorem pointMapRing_some {x y : F} (h : V.toAffine.Nonsingular x y) :
    ∃ h' : (V.map f).toAffine.Nonsingular (f x) (f y),
      pointMapRing f V (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

end PointMap

section Functorial

variable {𝒪₁ 𝒪₂ : Type*} [CommRing 𝒪₁] [IsDomain 𝒪₁] [IsDiscreteValuationRing 𝒪₁]
  [CommRing 𝒪₂] [IsDomain 𝒪₂] [IsDiscreteValuationRing 𝒪₂]
  (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra 𝒪₁ K₁] [IsFractionRing 𝒪₁ K₁] [Algebra 𝒪₂ K₂]
  [IsFractionRing 𝒪₂ K₂] {f : 𝒪₁ →+* 𝒪₂} [IsLocalHom f] {σ : K₁ →+* K₂}
  (hσ : σ.comp (algebraMap 𝒪₁ K₁) = (algebraMap 𝒪₂ K₂).comp f) (W : WeierstrassCurve 𝒪₁)

include hσ in
theorem map_curveK_eq :
    (W.map (algebraMap 𝒪₁ K₁)).map σ = (W.map f).map (algebraMap 𝒪₂ K₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, hσ]

theorem map_curveRed_eq :
    (W.map (residue 𝒪₁)).map (ResidueField.map f) = (W.map f).map (residue 𝒪₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, ResidueField.map_comp_residue]

include hσ in

theorem map_notMem_range {X : K₁} (hX : X ∉ Set.range (algebraMap 𝒪₁ K₁)) :
    σ X ∉ Set.range (algebraMap 𝒪₂ K₂) := by
  rintro ⟨s, hs⟩
  obtain ⟨t, htm, ht⟩ := exists_inv_mem_of_notMem_range K₁ hX
  have hX0 : X ≠ 0 := fun h => hX ⟨0, by rw [h, map_zero]⟩
  have h1 : algebraMap 𝒪₂ K₂ (s * f t) = 1 := by
    rw [map_mul, hs, ← RingHom.comp_apply, ← hσ, RingHom.comp_apply, ht, ← map_mul,
      mul_inv_cancel₀ hX0, map_one]
  have hu : IsUnit (f t) := isUnit_iff_exists_inv.mpr ⟨s,
    IsFractionRing.injective 𝒪₂ K₂ (by rw [mul_comm, h1, map_one])⟩
  exact (mem_maximalIdeal _).1 htm (isUnit_of_map_unit f t hu)

variable [W.IsElliptic] [DecidableEq K₁] [DecidableEq K₂] [DecidableEq (ResidueField 𝒪₁)]
  [DecidableEq (ResidueField 𝒪₂)]

theorem reducePoint_pointMapRing (P : (curveK K₁ W).Point) :
    reducePoint K₂ (W.map f) (pointCongr (map_curveK_eq K₁ K₂ hσ W)
        (pointMapRing σ (W.map (algebraMap 𝒪₁ K₁)) P)) =
      pointCongr (map_curveRed_eq W)
        (pointMapRing (ResidueField.map f) (W.map (residue 𝒪₁)) (reducePoint K₁ W P)) := by
  rcases point_cases K₁ W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rw [reducePoint_zero, map_zero, map_zero, map_zero, map_zero, reducePoint_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    rw [e, pointCongr_some, reducePoint_some_notMem K₂ (W.map f) _ (map_notMem_range K₁ K₂ hσ hX),
      reducePoint_some_notMem K₁ W h hX, map_zero, map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    have hx : σ (algebraMap 𝒪₁ K₁ x) = algebraMap 𝒪₂ K₂ (f x) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have hy : σ (algebraMap 𝒪₁ K₁ y) = algebraMap 𝒪₂ K₂ (f y) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have h₂ : (curveK K₂ (W.map f)).Nonsingular (algebraMap 𝒪₂ K₂ (f x))
        (algebraMap 𝒪₂ K₂ (f y)) := by
      have := (map_curveK_eq K₁ K₂ hσ W) ▸ h'
      rwa [hx, hy] at this
    have n₁ := nonsingular_residue_of_isElliptic K₁ W h.1
    have n₂ := nonsingular_residue_of_isElliptic K₂ (W.map f) h₂.1
    obtain ⟨n₁', e₁⟩ := pointMapRing_some (ResidueField.map f) (W.map (residue 𝒪₁)) n₁
    have e₂ : pointCongr (map_curveK_eq K₁ K₂ hσ W) (.some _ _ h') = .some _ _ h₂ := by
      rw [pointCongr_some, Point.some.injEq]
      exact ⟨hx, hy⟩
    rw [e, e₂, reducePoint_some_integral K₂ (W.map f) h₂ n₂, reducePoint_some_integral K₁ W h n₁,
      e₁, pointCongr_some, Point.some.injEq, ResidueField.map_residue, ResidueField.map_residue]
    exact ⟨rfl, rfl⟩

end Functorial

section FF

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

abbrev gaussCurve : WeierstrassCurve (gaussRing W) := W'.map (algebraMap 𝒪 (gaussRing W))

theorem gaussCurve_map_functionField :
    (gaussCurve W W').map (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField := by
  show W'.map ((algebraMap (gaussRing W) _).comp (algebraMap 𝒪 (gaussRing W))) =
    W'.map ((algebraMap K _).comp (algebraMap 𝒪 K))
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

theorem gaussCurve_map_residue :
    ((gaussCurve W W').map (residue (gaussRing W))).map (gaussResidue W) =
      (W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField := by
  simp only [gaussCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [gaussResidue_residue_algebraMap, ← IsScalarTower.algebraMap_apply]

variable [W'.IsElliptic]

def reduceFF : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point →+
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).toAffine.Point :=
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  (pointCongr (gaussCurve_map_residue W W')).toAddMonoidHom.comp
    ((pointMapRing (gaussResidue W) _).comp
      ((reductionHom (W.baseChange K).toAffine.FunctionField (gaussCurve W W')).comp
        (pointCongr (gaussCurve_map_functionField K W W').symm).toAddMonoidHom))

end FF

end

end GroundTheory.Global
