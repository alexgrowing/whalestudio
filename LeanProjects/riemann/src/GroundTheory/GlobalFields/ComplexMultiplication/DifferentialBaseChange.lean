import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstant

namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F']

section Emb

variable (E : WeierstrassCurve F) [E.IsElliptic]

omit [E.IsElliptic] in
theorem transcendental_genX_baseChange : Transcendental F (genX (E.baseChange F')) :=
  Transcendental.restrictScalars (algebraMap F F').injective (transcendental_genX _)

noncomputable def bcEmb :
    E.toAffine.FunctionField →ₐ[F] (E.baseChange F').toAffine.FunctionField :=
  liftPoint E (L := (E.baseChange F').toAffine.FunctionField) (u := genX (E.baseChange F'))
    (v := genY (E.baseChange F')) (equation_gen (E.baseChange F'))
    (transcendental_genX_baseChange E)

omit [E.IsElliptic] in
theorem bcEmb_genX : bcEmb (F' := F') E (genX E) = genX (E.baseChange F') :=
  liftPoint_genX _ _ _

omit [E.IsElliptic] in
theorem bcEmb_genY : bcEmb (F' := F') E (genY E) = genY (E.baseChange F') :=
  liftPoint_genY _ _ _

theorem map_bcEmb_genericPoint [DecidableEq F'] :
    Point.map (bcEmb (F' := F') E) (genericPoint E) =
      (genericPoint (E.baseChange F') :
        (E.baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) :=
  map_liftPoint_genericPoint E _ _

omit [E.IsElliptic] in

theorem transcendental_bcEmb {z : E.toAffine.FunctionField} (hz : Transcendental F z) :
    Transcendental F' (bcEmb (F' := F') E z) := by
  set K' := (E.baseChange F').toAffine.FunctionField
  set ι := bcEmb (F' := F') E
  intro halg
  have : FiniteDimensional F⟮z⟯ E.toAffine.FunctionField :=
    finiteDimensional_adjoin_of_transcendental E hz
  set A : IntermediateField F' K' := F'⟮ι z⟯
  have hA : Algebra.IsAlgebraic F' A := isAlgebraic_adjoin_simple halg.isIntegral
  have hmem : ∀ w ∈ F⟮z⟯, ι w ∈ A := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact mem_adjoin_simple_self F' _
    | algebraMap x =>
      rw [ι.commutes, IsScalarTower.algebraMap_apply F F' K']
      exact A.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let g : F⟮z⟯ →+* A :=
    { toFun := fun w => ⟨ι w, hmem w w.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hint : IsIntegral F⟮z⟯ (genX E) := Algebra.IsIntegral.isIntegral _
  set p := minpoly F⟮z⟯ (genX E)
  have hq : aeval (genX (E.baseChange F')) (p.map g) = 0 := by
    have e : (algebraMap A K').comp g = ι.toRingHom.comp (algebraMap F⟮z⟯ E.toAffine.FunctionField) := by
      ext w; rfl
    rw [aeval_def, eval₂_map, e, ← bcEmb_genX]
    have h2 := hom_eval₂ p (algebraMap F⟮z⟯ E.toAffine.FunctionField) ι.toRingHom (genX E)
    rw [← aeval_def, minpoly.aeval, map_zero] at h2
    exact h2.symm
  have hX : IsAlgebraic A (genX (E.baseChange F')) :=
    ⟨p.map g, (minpoly.monic hint).map g |>.ne_zero, hq⟩
  exact transcendental_genX (E.baseChange F') (hX.restrictScalars F')

end Emb

section Isog

variable [DecidableEq F'] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

noncomputable def bcPoint (φ : Isogeny E E') :
    ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point :=
  Point.map (W' := E') (bcEmb (F' := F') E) φ.1

omit [DecidableEq F'] [E.IsElliptic] [E'.IsElliptic] in
theorem map_restrictScalars_eq {L : Type u} [Field L] [Algebra F' L] [DecidableEq L]
    (g : (E.baseChange F').toAffine.FunctionField →ₐ[F'] L)
    (X : (E'.baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) :
    letI : Algebra F L := ((algebraMap F' L).comp (algebraMap F F')).toAlgebra
    haveI : IsScalarTower F F' L := IsScalarTower.of_algebraMap_eq' rfl
    Point.map (W' := E') (g.restrictScalars F) X =
      Point.map (W' := E'.baseChange F') g
        (X : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) := by
  cases X <;> rfl

omit [DecidableEq F'] in
theorem isIsogeny_bcPoint (φ : Isogeny E E') :
    IsIsogeny (E.baseChange F') (E'.baseChange F') (bcPoint φ) := by
  rw [isIsogeny_iff]
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨x, y, h, he, hx⟩, -⟩ := φ.2
    show IsGenPt (E'.baseChange F') (Point.map (W' := E') (bcEmb (F' := F') E) φ.1)
    rw [he]
    exact transcendental_bcEmb E hx
  · rw [respectsAdd_iff]
    intro L _ _ _ P₁ P₂ h₁ h₂ h₃
    let _ : Algebra F L := ((algebraMap F' L).comp (algebraMap F F')).toAlgebra
    have _ : IsScalarTower F F' L := IsScalarTower.of_algebraMap_eq' rfl
    have res : ∀ P : ((E.baseChange F').baseChange L).toAffine.Point,
        IsGenPt (E.baseChange F') P → IsGenPt E (P : (E.baseChange L).toAffine.Point) := by
      intro P hP
      cases P with
      | zero => exact hP.elim
      | some x y h => exact Transcendental.restrictScalars (algebraMap F F').injective hP
    have key : ∀ (P : ((E.baseChange F').baseChange L).toAffine.Point)
        (hP : IsGenPt (E.baseChange F') P),
        Point.map (genEval (E.baseChange F') P hP) (bcPoint φ) =
          φ.app (P : (E.baseChange L).toAffine.Point) (res P hP) := by
      intro P hP
      have hg : ((genEval (E.baseChange F') P hP).restrictScalars F).comp (bcEmb (F' := F') E) =
          genEval E (P : (E.baseChange L).toAffine.Point) (res P hP) := by
        refine eq_genEval E _ ?_ _
        cases P with
        | zero => exact hP.elim
        | some u v hv =>
          simp only [GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
          congr 1
          · show genEval (E.baseChange F') _ hP (bcEmb (F' := F') E (genX E)) = u
            rw [bcEmb_genX]; exact genEval_genX (E.baseChange F') _ hP
          · show genEval (E.baseChange F') _ hP (bcEmb (F' := F') E (genY E)) = v
            rw [bcEmb_genY]; exact genEval_genY (E.baseChange F') _ hP
      unfold Isogeny.app
      rw [← hg, ← Point.map_map, map_restrictScalars_eq]
      rfl
    rw [key _ h₃, key _ h₁, key _ h₂]
    exact φ.app_add (res _ h₁) (res _ h₂) (res _ h₃)

noncomputable def isogBaseChange (φ : Isogeny E E') : Isogeny (E.baseChange F') (E'.baseChange F') :=
  ⟨bcPoint φ, isIsogeny_bcPoint φ⟩

theorem isogBaseChange_val (φ : Isogeny E E') :
    (isogBaseChange (F' := F') φ).1 = Point.map (W' := E') (bcEmb (F' := F') E) φ.1 := rfl

end Isog

section Diff

variable (E : WeierstrassCurve F) [E.IsElliptic]

noncomputable def bcDiff :
    Ω[E.toAffine.FunctionField⁄F] →+ Ω[(E.baseChange F').toAffine.FunctionField⁄F'] :=
  letI : Algebra E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    (bcEmb (F' := F') E).toRingHom.toAlgebra
  haveI : IsScalarTower F E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun a => ((bcEmb (F' := F') E).commutes a).symm
  (KaehlerDifferential.map F F' E.toAffine.FunctionField
    (E.baseChange F').toAffine.FunctionField).toAddMonoidHom

omit [E.IsElliptic] in
theorem bcDiff_D (a : E.toAffine.FunctionField) :
    bcDiff (F' := F') E (D F _ a) = D F' _ (bcEmb (F' := F') E a) := by
  let _ : Algebra E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    (bcEmb (F' := F') E).toRingHom.toAlgebra
  have _ : IsScalarTower F E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun a => ((bcEmb (F' := F') E).commutes a).symm
  exact KaehlerDifferential.map_D F F' _ _ a

omit [E.IsElliptic] in
theorem bcDiff_smul (a : E.toAffine.FunctionField) (η : Ω[E.toAffine.FunctionField⁄F]) :
    bcDiff (F' := F') E (a • η) = bcEmb (F' := F') E a • bcDiff E η := by
  let _ : Algebra E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    (bcEmb (F' := F') E).toRingHom.toAlgebra
  have _ : IsScalarTower F E.toAffine.FunctionField (E.baseChange F').toAffine.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun a => ((bcEmb (F' := F') E).commutes a).symm
  show KaehlerDifferential.map F F' _ _ (a • η) = _
  rw [LinearMap.map_smul]
  exact (algebraMap_smul (E.baseChange F').toAffine.FunctionField a _).symm

variable [DecidableEq F'] {E} {E' : WeierstrassCurve F}

omit [E.IsElliptic] [DecidableEq F'] in

theorem bcDiff_omegaAt (P : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) :
    bcDiff (F' := F') E (omegaAt E' P) =
      omegaAt (E'.baseChange F') (Point.map (W' := E') (bcEmb (F' := F') E) P :
        ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point) := by
  rcases P with _ | ⟨x, y, h⟩
  · show bcDiff E (omegaAt E' 0) = omegaAt (E'.baseChange F') 0
    rw [omegaAt_zero, omegaAt_zero, map_zero]
  · obtain ⟨s, t⟩ := omegaAt_some_spec E' h
    have c1 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₁ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₁ := ((bcEmb (F' := F') E).commutes E'.a₁).symm
    have c2 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₂ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₂ := ((bcEmb (F' := F') E).commutes E'.a₂).symm
    have c3 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₃ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₃ := ((bcEmb (F' := F') E).commutes E'.a₃).symm
    have c4 : ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).a₄ =
        bcEmb (F' := F') E (E'.baseChange E.toAffine.FunctionField).a₄ := ((bcEmb (F' := F') E).commutes E'.a₄).symm
    refine (omegaAt_some_eq (E'.baseChange F') _ ?_ ?_).symm
    · rw [c1, c3, ← bcDiff_D, ← s, bcDiff_smul]
      simp only [map_add, map_mul, map_ofNat]
    · rw [c1, c2, c4, ← bcDiff_D, ← t, bcDiff_smul]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]

variable (E) in

theorem bcDiff_invariantDifferential :
    bcDiff (F' := F') E (invariantDifferential E) = invariantDifferential (E.baseChange F') := by
  rw [invariantDifferential, bcDiff_omegaAt, map_bcEmb_genericPoint]
  rfl

variable [E'.IsElliptic]

theorem bcDiff_isogenyPullback (φ : Isogeny E E') :
    bcDiff (F' := F') E (isogenyPullback φ (invariantDifferential E')) =
      isogenyPullback (isogBaseChange (F' := F') φ) (invariantDifferential (E'.baseChange F')) := by
  rw [isogenyPullback_invariantDifferential, isogenyPullback_invariantDifferential, bcDiff_omegaAt]
  rfl

theorem isogCoeff_isogBaseChange (φ : Isogeny E E') :
    isogCoeff (isogBaseChange (F' := F') φ) = bcEmb (F' := F') E (isogCoeff φ) := by
  refine invCoeff_eq (E.baseChange F') ?_
  rw [← bcDiff_invariantDifferential, ← bcDiff_smul, ← isogenyPullback_invariantDifferential_eq_smul,
    bcDiff_isogenyPullback, isogenyPullback_invariantDifferential]

end Diff

end GroundTheory.Global
