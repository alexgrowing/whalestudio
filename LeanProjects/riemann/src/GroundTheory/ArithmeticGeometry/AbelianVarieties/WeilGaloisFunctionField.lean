import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsPullback
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TorsionGalois

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open scoped Polynomial.Bivariate

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L] (W₀ : WeierstrassCurve K)

section Coord

theorem polynomial_map_galois (σ : L ≃ₐ[K] L) :
    (W₀.baseChange L).toAffine.polynomial.map (mapRingHom (σ : L →+* L)) =
      (W₀.baseChange L).toAffine.polynomial := by
  have h1 : (W₀.baseChange L).map (σ : L →+* L) = W₀.baseChange L :=
    WeierstrassCurve.map_baseChange (R := K) (S := K) W₀ (σ : L →ₐ[K] L)
  rw [← Affine.map_polynomial]
  exact congrArg (fun V : WeierstrassCurve L => V.toAffine.polynomial) h1

noncomputable def galCoord (σ : L ≃ₐ[K] L) :
    (W₀.baseChange L).toAffine.CoordinateRing ≃+* (W₀.baseChange L).toAffine.CoordinateRing :=
  Ideal.quotientEquiv _ _ (Polynomial.mapEquiv (Polynomial.mapEquiv σ.toRingEquiv)) (by
    have h : (Polynomial.mapEquiv (Polynomial.mapEquiv σ.toRingEquiv))
        (W₀.baseChange L).toAffine.polynomial = (W₀.baseChange L).toAffine.polynomial :=
      polynomial_map_galois W₀ σ
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun q => Ideal.span {q}) h.symm)

theorem galCoord_mk (σ : L ≃ₐ[K] L) (p : L[X][Y]) :
    galCoord W₀ σ (CoordinateRing.mk _ p) =
      CoordinateRing.mk _ (p.map (mapRingHom (σ : L →+* L))) :=
  rfl

end Coord

section FunctionField

noncomputable def galFF (σ : L ≃ₐ[K] L) :
    (W₀.baseChange L).toAffine.FunctionField ≃+* (W₀.baseChange L).toAffine.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (galCoord W₀ σ)

theorem galFF_algebraMap_coord (σ : L ≃ₐ[K] L) (a : (W₀.baseChange L).toAffine.CoordinateRing) :
    galFF W₀ σ (algebraMap _ (W₀.baseChange L).toAffine.FunctionField a) =
      algebraMap _ (W₀.baseChange L).toAffine.FunctionField (galCoord W₀ σ a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem galFF_algebraMap (σ : L ≃ₐ[K] L) (c : L) :
    galFF W₀ σ (algebraMap L (W₀.baseChange L).toAffine.FunctionField c) =
      algebraMap L (W₀.baseChange L).toAffine.FunctionField (σ c) := by
  have e : ∀ a : L, algebraMap L (W₀.baseChange L).toAffine.FunctionField a =
      algebraMap (W₀.baseChange L).toAffine.CoordinateRing _
        (CoordinateRing.mk _ (C (C a))) := fun a => rfl
  rw [e, e, galFF_algebraMap_coord, galCoord_mk]
  simp

theorem galFF_genX (σ : L ≃ₐ[K] L) : galFF W₀ σ (genX (W₀.baseChange L)) = genX (W₀.baseChange L) := by
  rw [genX, galFF_algebraMap_coord, galCoord_mk]
  simp

theorem galFF_genY (σ : L ≃ₐ[K] L) : galFF W₀ σ (genY (W₀.baseChange L)) = genY (W₀.baseChange L) := by
  rw [genY, galFF_algebraMap_coord, galCoord_mk]
  simp

theorem galFF_algebraMap_base (σ : L ≃ₐ[K] L) (k : K) :
    galFF W₀ σ (algebraMap K (W₀.baseChange L).toAffine.FunctionField k) =
      algebraMap K (W₀.baseChange L).toAffine.FunctionField k := by
  rw [IsScalarTower.algebraMap_apply K L, galFF_algebraMap, AlgEquiv.commutes]

noncomputable def galFFAlg (σ : L ≃ₐ[K] L) :
    (W₀.baseChange L).toAffine.FunctionField ≃ₐ[K] (W₀.baseChange L).toAffine.FunctionField :=
  AlgEquiv.ofRingEquiv (f := galFF W₀ σ) (galFF_algebraMap_base W₀ σ)

theorem galFF_symm_algebraMap (σ : L ≃ₐ[K] L) (c : L) :
    (galFF W₀ σ).symm (algebraMap L (W₀.baseChange L).toAffine.FunctionField c) =
      algebraMap L (W₀.baseChange L).toAffine.FunctionField (σ.symm c) := by
  rw [RingEquiv.symm_apply_eq, galFF_algebraMap, AlgEquiv.apply_symm_apply]

theorem galFF_symm_genX (σ : L ≃ₐ[K] L) :
    (galFF W₀ σ).symm (genX (W₀.baseChange L)) = genX (W₀.baseChange L) := by
  rw [RingEquiv.symm_apply_eq, galFF_genX]

theorem galFF_symm_genY (σ : L ≃ₐ[K] L) :
    (galFF W₀ σ).symm (genY (W₀.baseChange L)) = genY (W₀.baseChange L) := by
  rw [RingEquiv.symm_apply_eq, galFF_genY]

theorem map_galFF_curve (σ : L ≃ₐ[K] L) :
    ((W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField).map
      (galFF W₀ σ : _ →+* _) =
      (W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField := by
  have e : ∀ a : K, galFF W₀ σ (algebraMap L (W₀.baseChange L).toAffine.FunctionField
      (algebraMap K L a)) = algebraMap L _ (algebraMap K L a) := fun a => by
    rw [galFF_algebraMap, AlgEquiv.commutes]
  ext <;> exact e _

noncomputable def galConj (σ : L ≃ₐ[K] L)
    (ψ : (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField) :
    (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField :=
  { ((galFF W₀ σ).toRingHom.comp ψ.toRingHom).comp (galFF W₀ σ).symm.toRingHom with
    commutes' := fun c => by
      change galFF W₀ σ (ψ ((galFF W₀ σ).symm (algebraMap L _ c))) = algebraMap L _ c
      rw [galFF_symm_algebraMap, ψ.commutes, galFF_algebraMap, AlgEquiv.apply_symm_apply] }

theorem galConj_apply (σ : L ≃ₐ[K] L)
    (ψ : (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField)
    (f : (W₀.baseChange L).toAffine.FunctionField) :
    galConj W₀ σ ψ f = galFF W₀ σ (ψ ((galFF W₀ σ).symm f)) := rfl

end FunctionField

section AutPoint

variable {Fd : Type*} [Field Fd] (V : WeierstrassCurve Fd) (τ : Fd ≃+* Fd)
  (hV : V.map (τ : Fd →+* Fd) = V)

include hV in
theorem nonsingular_aut {x y : Fd} (h : V.toAffine.Nonsingular x y) :
    V.toAffine.Nonsingular (τ x) (τ y) := by
  have h1 := (Affine.map_nonsingular (W := V.toAffine) (f := (τ : Fd →+* Fd)) τ.injective x y).mpr h
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

include hV in
theorem negY_aut (x y : Fd) : V.toAffine.negY (τ x) (τ y) = τ (V.toAffine.negY x y) := by
  have h1 := Affine.map_negY (W' := V.toAffine) (τ : Fd →+* Fd) x y
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

include hV in
theorem addX_aut (x₁ x₂ ℓ : Fd) :
    V.toAffine.addX (τ x₁) (τ x₂) (τ ℓ) = τ (V.toAffine.addX x₁ x₂ ℓ) := by
  have h1 := Affine.map_addX (W' := V.toAffine) (τ : Fd →+* Fd) (x₁ := x₁) (x₂ := x₂) (ℓ := ℓ)
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

include hV in
theorem addY_aut (x₁ x₂ y₁ ℓ : Fd) :
    V.toAffine.addY (τ x₁) (τ x₂) (τ y₁) (τ ℓ) = τ (V.toAffine.addY x₁ x₂ y₁ ℓ) := by
  have h1 := Affine.map_addY (W' := V.toAffine) (τ : Fd →+* Fd) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (ℓ := ℓ)
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

variable [DecidableEq Fd]

include hV in
theorem slope_aut (x₁ x₂ y₁ y₂ : Fd) :
    V.toAffine.slope (τ x₁) (τ x₂) (τ y₁) (τ y₂) = τ (V.toAffine.slope x₁ x₂ y₁ y₂) := by
  have h1 := Affine.map_slope (W := V.toAffine) (τ : Fd →+* Fd) x₁ x₂ y₁ y₂
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

noncomputable def autPoint : V.toAffine.Point →+ V.toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (τ x) (τ y) (nonsingular_aut V τ hV h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, Affine.Point.add_of_Y_eq (congr_arg τ hxy.1)
        (by rw [hxy.2, negY_aut V τ hV])]
    · have hxy' : ¬(τ x₁ = τ x₂ ∧ τ y₁ = V.toAffine.negY (τ x₂) (τ y₂)) := fun h =>
        hxy ⟨τ.injective h.1, τ.injective (by rw [h.2, negY_aut V τ hV])⟩
      rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
      change Affine.Point.some _ _ _ = Affine.Point.some _ _ _
      simp only [Affine.Point.some.injEq]
      exact ⟨by rw [slope_aut V τ hV, addX_aut V τ hV],
        by rw [slope_aut V τ hV, addY_aut V τ hV]⟩

theorem autPoint_some {x y : Fd} (h : V.toAffine.Nonsingular x y) :
    autPoint V τ hV (.some x y h) = .some (τ x) (τ y) (nonsingular_aut V τ hV h) := rfl

end AutPoint

section Points

variable [DecidableEq L] [W₀.IsElliptic]

noncomputable def galFFPoint (σ : L ≃ₐ[K] L) :
    ((W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField).toAffine.Point →+
      ((W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField).toAffine.Point :=
  autPoint _ (galFF W₀ σ) (map_galFF_curve W₀ σ)

omit [DecidableEq L] in

theorem galFFPoint_genericPoint (σ : L ≃ₐ[K] L) :
    galFFPoint W₀ σ (genericPoint (W₀.baseChange L)) = genericPoint (W₀.baseChange L) := by
  rw [genericPoint, galFFPoint, autPoint_some]
  simp only [Affine.Point.some.injEq]
  exact ⟨galFF_genX W₀ σ, galFF_genY W₀ σ⟩

omit [W₀.IsElliptic] in

theorem galFFPoint_constPoint (σ : L ≃ₐ[K] L) (R : (W₀.baseChange L).toAffine.Point) :
    galFFPoint W₀ σ (constPoint (W₀.baseChange L) R) =
      constPoint (W₀.baseChange L) (galPointsHom K L W₀ σ R) := by
  cases R with
  | zero =>
    have h0 : (Affine.Point.zero : (W₀.baseChange L).toAffine.Point) = 0 := rfl
    rw [h0, map_zero, map_zero, map_zero, map_zero]
  | some x y h =>
    change autPoint _ _ _ (Affine.Point.some _ _ _) = Affine.Point.some _ _ _
    rw [autPoint_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨galFF_algebraMap W₀ σ x, galFF_algebraMap W₀ σ y⟩

omit [DecidableEq L] in
theorem map_galConj_genericPoint (σ : L ≃ₐ[K] L)
    (ψ : (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField) :
    Affine.Point.map (galConj W₀ σ ψ) (genericPoint (W₀.baseChange L)) =
      galFFPoint W₀ σ (Affine.Point.map ψ (genericPoint (W₀.baseChange L))) := by
  rw [genericPoint, Affine.Point.map_some, Affine.Point.map_some, galFFPoint, autPoint_some]
  simp only [Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [galConj_apply, galFF_symm_genX]
  · rw [galConj_apply, galFF_symm_genY]
variable [IsAlgClosed L]

theorem galConj_translate (σ : L ≃ₐ[K] L) (R : (W₀.baseChange L).toAffine.Point) :
    galConj W₀ σ (translate (W₀.baseChange L) R) =
      translate (W₀.baseChange L) (galPointsHom K L W₀ σ R) := by
  apply algHom_eq_of_map_genericPoint
  rw [map_galConj_genericPoint, map_translate_genericPoint, map_add, galFFPoint_genericPoint,
    galFFPoint_constPoint, map_translate_genericPoint]

theorem galFF_translate (σ : L ≃ₐ[K] L) (R : (W₀.baseChange L).toAffine.Point)
    (f : (W₀.baseChange L).toAffine.FunctionField) :
    galFF W₀ σ (translate (W₀.baseChange L) R f) =
      translate (W₀.baseChange L) (galPointsHom K L W₀ σ R) (galFF W₀ σ f) := by
  rw [← galConj_translate, galConj_apply, RingEquiv.symm_apply_apply]

end Points

end GroundTheory.Arith.Abelian
