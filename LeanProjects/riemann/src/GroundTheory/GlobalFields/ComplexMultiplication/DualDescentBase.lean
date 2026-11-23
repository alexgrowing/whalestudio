import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DualDescentField
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDegree
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualQuadratic

namespace GroundTheory.Global

open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section BaseChange

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem x_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).x = bcEmb (F' := Ω) E φ.x := by
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  simp only [Isogeny.x, isogBaseChange_val, he]
  rfl

theorem y_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).y = bcEmb (F' := Ω) E φ.y := by
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  simp only [Isogeny.y, isogBaseChange_val, he]
  rfl

theorem isogBaseChange_injective :
    Function.Injective (isogBaseChange (F' := Ω) : Isogeny E E' → _) := by
  intro φ ψ h
  apply Isogeny.ext_xy
  · have e := congrArg Isogeny.x h
    rw [x_isogBaseChange, x_isogBaseChange] at e
    exact (bcEmb (F' := Ω) E).injective e
  · have e := congrArg Isogeny.y h
    rw [y_isogBaseChange, y_isogBaseChange] at e
    exact (bcEmb (F' := Ω) E).injective e

theorem isogBaseChange_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    isogBaseChange (F' := Ω) (ψ.comp φ) =
      (isogBaseChange (F' := Ω) ψ).comp (isogBaseChange (F' := Ω) φ) := by
  apply Isogeny.ext_xy
  · rw [x_isogBaseChange, Isogeny.comp_alt, Isogeny.comp_alt, x_isogBaseChange,
      comap_isogBaseChange_bcEmb]
  · rw [y_isogBaseChange, Isogeny.comp_y, Isogeny.comp_y, y_isogBaseChange,
      comap_isogBaseChange_bcEmb]

theorem isogBaseChange_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    isogBaseChange (F' := Ω) (mulIsogeny E n hn) = mulIsogeny (E.baseChange Ω) n hn := by
  classical
  apply Subtype.ext
  show Point.map (W' := E) (bcEmb (F' := Ω) E) (n • genericPoint E) =
    n • genericPoint (E.baseChange Ω)
  rw [map_zsmul, map_bcEmb_genericPoint]
  rfl

theorem degree_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).degree = φ.degree := by
  obtain ⟨r, hr⟩ := φ.exists_ratEmb_eq_x
  have hcop : IsCoprime (r.num.map (algebraMap F Ω)) (r.denom.map (algebraMap F Ω)) := by
    simpa using r.isCoprime_num_denom.map (mapRingHom (algebraMap F Ω))
  obtain ⟨h1, h2⟩ := num_denom_div_of_isCoprime (r.monic_denom.map (algebraMap F Ω)) hcop
  have hb : ∀ p : F[X], bcEmb (F' := Ω) E (aeval (genX E) p) =
      aeval (genX (E.baseChange Ω)) (p.map (algebraMap F Ω)) := by
    intro p
    rw [← aeval_algHom_apply, bcEmb_genX, aeval_map_algebraMap]
  have hx : ratEmb (E.baseChange Ω) (algebraMap _ _ (r.num.map (algebraMap F Ω)) /
      algebraMap _ _ (r.denom.map (algebraMap F Ω))) = (isogBaseChange (F' := Ω) φ).x := by
    rw [x_isogBaseChange, ← hr, ratEmb_div]
    conv_rhs => rw [← RatFunc.num_div_denom r]
    rw [ratEmb_div, map_div₀, hb, hb]
  rw [φ.degree_eq_max_natDegree hr, (isogBaseChange (F' := Ω) φ).degree_eq_max_natDegree hx, h1, h2,
    natDegree_map_eq_of_injective (algebraMap F Ω).injective,
    natDegree_map_eq_of_injective (algebraMap F Ω).injective]

end BaseChange

section Dual

variable {F : Type u} [Field F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

theorem isogeny_degree_pos (φ : Isogeny E E') : 0 < φ.degree := by
  classical
  rw [← degree_isogBaseChange (Ω := AlgebraicClosure F)]
  exact Isogeny.degree_pos _

theorem isogeny_degree_ne_zero (φ : Isogeny E E') : (φ.degree : ℤ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (isogeny_degree_pos φ).ne'

theorem mulIsogeny_eq_dual_comp_isogBaseChange [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    mulIsogeny (E.baseChange (AlgebraicClosure F)) φ.degree (isogeny_degree_ne_zero φ) =
      (isogBaseChange (F' := AlgebraicClosure F) φ).dual.comp (isogBaseChange φ) := by
  rw [Isogeny.dual_comp]
  exact mulIsogeny_congr (by rw [degree_isogBaseChange]) _ _

theorem mulIsogeny_comap_mem_fieldRange (φ : Isogeny E E') (f : E.toAffine.FunctionField) :
    (mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap f ∈ φ.comap.fieldRange := by
  classical
  apply mem_fieldRange_comap_of_bcEmb (Ω := AlgebraicClosure F) φ
  rw [← comap_isogBaseChange_bcEmb, isogBaseChange_mulIsogeny,
    mulIsogeny_eq_dual_comp_isogBaseChange, Isogeny.comap_comp, AlgHom.comp_apply]
  exact ⟨_, rfl⟩

noncomputable def dualComapOver (φ : Isogeny E E') :
    E.toAffine.FunctionField →ₐ[F] E'.toAffine.FunctionField :=
  φ.comap.equivFieldRange.symm.toAlgHom.comp
    ((mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (mulIsogeny_comap_mem_fieldRange φ))

theorem comap_dualComapOver (φ : Isogeny E E') (f : E.toAffine.FunctionField) :
    φ.comap (dualComapOver φ f) = (mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap f := by
  have := φ.comap.equivFieldRange.apply_symm_apply
    ((mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (mulIsogeny_comap_mem_fieldRange φ) f)
  exact congrArg Subtype.val this

noncomputable def dualPtOver (φ : Isogeny E E') : (E.baseChange E'.toAffine.FunctionField).toAffine.Point :=
  Point.map (dualComapOver φ) (genericPoint E)

theorem isGenPt_dualPtOver (φ : Isogeny E E') : IsGenPt E (dualPtOver φ) :=
  isGenPt_map_genericPoint E _

theorem map_bcEmb_dualPtOver [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) E') (dualPtOver φ) :
      ((E.baseChange (AlgebraicClosure F)).baseChange
        (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) =
      (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1 := by
  have hD : (bcEmb (F' := AlgebraicClosure F) E').comp (dualComapOver φ) =
      ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap.restrictScalars F).comp
        (bcEmb (F' := AlgebraicClosure F) E) := by
    apply AlgHom.ext
    intro f
    have key : (isogBaseChange (F' := AlgebraicClosure F) φ).comap
        (bcEmb (F' := AlgebraicClosure F) E' (dualComapOver φ f)) =
        (isogBaseChange (F' := AlgebraicClosure F) φ).comap
          ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap
            (bcEmb (F' := AlgebraicClosure F) E f)) := by
      rw [comap_isogBaseChange_bcEmb, comap_dualComapOver, ← comap_isogBaseChange_bcEmb,
        isogBaseChange_mulIsogeny, mulIsogeny_eq_dual_comp_isogBaseChange, Isogeny.comap_comp,
        AlgHom.comp_apply]
    exact (isogBaseChange (F' := AlgebraicClosure F) φ).comap.injective key
  have hcast : ∀ X : (E.baseChange (E.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point,
      Point.map (W' := E)
          ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap.restrictScalars F) X =
        Point.map (W' := E.baseChange (AlgebraicClosure F))
          (isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap X := by
    intro X
    cases X <;> rfl
  rw [dualPtOver, Point.map_map, hD, ← Point.map_map, hcast, map_bcEmb_genericPoint,
    Isogeny.map_comap_genericPoint]

end Dual

end GroundTheory.Global
