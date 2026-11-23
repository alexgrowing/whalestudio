import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilFixedField

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F]

section Finite

variable (E : WeierstrassCurve F)

omit [Field F] in
theorem trdeg_functionField_le_one [Field F] : Algebra.trdeg F E.toAffine.FunctionField ≤ 1 := by
  have hfin : FiniteDimensional F⟮genX E⟯ E.toAffine.FunctionField :=
    Module.finite_of_finrank_eq_succ (finrank_adjoin_genX E)
  open IntermediateField.algebraAdjoinAdjoin in
  have : Algebra.IsAlgebraic (Algebra.adjoin F {genX E}) E.toAffine.FunctionField :=
    Algebra.IsAlgebraic.trans (Algebra.adjoin F {genX E}) F⟮genX E⟯ E.toAffine.FunctionField
  have := Algebra.IsAlgebraic.trdeg_le_cardinalMk F ({genX E} : Set E.toAffine.FunctionField)
  simpa using this

theorem finiteDimensional_adjoin_of_transcendental {z : E.toAffine.FunctionField}
    (hz : Transcendental F z) : FiniteDimensional F⟮z⟯ E.toAffine.FunctionField := by
  let x : PUnit.{u + 1} → E.toAffine.FunctionField := fun _ => z
  have hind : AlgebraicIndependent F x := (algebraicIndependent_singleton_iff PUnit.unit).mpr hz
  have hb : IsTranscendenceBasis F x :=
    hind.isTranscendenceBasis_of_trdeg_le
      ((trdeg_functionField_le_one E).trans_lt Cardinal.one_lt_aleph0)
      (by rw [Cardinal.mk_punit]; exact trdeg_functionField_le_one E)
  have halg := hb.isAlgebraic
  have hrange : Set.range x = {z} := Set.range_const
  have hle : Algebra.adjoin F (Set.range x) ≤ (F⟮z⟯).toSubalgebra := by
    rw [hrange]; exact algebra_adjoin_le_adjoin F _
  have hint : ∀ w : E.toAffine.FunctionField, IsIntegral F⟮z⟯ w := fun w =>
    (IsAlgebraic.tower_top_of_subalgebra_le hle (halg.isAlgebraic w)).isIntegral
  have htop : F⟮z⟯⟮genX E, genY E⟯ = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F), restrictScalars_adjoin,
      eq_top_iff, ← adjoin_genX_genY E]
    exact adjoin.mono _ _ _ Set.subset_union_right
  have : FiniteDimensional F⟮z⟯ F⟮z⟯⟮genX E, genY E⟯ :=
    IntermediateField.finiteDimensional_adjoin (fun w _ => hint w)
  rw [htop] at this
  exact (IntermediateField.topEquiv (F := F⟮z⟯) (E := E.toAffine.FunctionField)).toLinearEquiv.finiteDimensional

end Finite

section Points

variable [IsAlgClosed F] [DecidableEq F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic]
  [E'.IsElliptic] [E''.IsElliptic]

namespace Isogeny

omit [IsAlgClosed F] [DecidableEq F] in

theorem degree_pos (φ : Isogeny E E') : 0 < φ.degree := by
  have hfin := finiteDimensional_adjoin_of_transcendental E φ.transcendental_alt
  have hle : F⟮φ.x⟯ ≤ φ.comap.fieldRange := adjoin_simple_le_iff.mpr ⟨genX E', φ.comap_genX⟩
  have t := relfinrank_mul_relfinrank hle (le_top : φ.comap.fieldRange ≤ ⊤)
  have hpos : 0 < relfinrank F⟮φ.x⟯ ⊤ := by
    rw [relfinrank_top_right]; exact Module.finrank_pos
  rw [degree, ← relfinrank_top_right]
  by_contra h
  push_neg at h
  rw [Nat.le_zero.mp h, mul_zero] at t
  omega

omit [IsAlgClosed F] [DecidableEq F] in
theorem finiteDimensional (φ : Isogeny E E') :
    FiniteDimensional φ.comap.fieldRange E.toAffine.FunctionField :=
  Module.finite_of_finrank_pos φ.degree_pos

omit [IsAlgClosed F] [DecidableEq F] in

theorem degree_eq_one_of_comap_eq (ψ : Isogeny E E) {z : E.toAffine.FunctionField}
    (hz : Transcendental F z) (h : ψ.comap z = z) : ψ.degree = 1 := by
  have hfin := finiteDimensional_adjoin_of_transcendental E hz
  have hle : F⟮z⟯ ≤ ψ.comap.fieldRange := adjoin_simple_le_iff.mpr ⟨z, h⟩
  have t := relfinrank_mul_relfinrank hle (le_top : ψ.comap.fieldRange ≤ ⊤)
  have e : relfinrank F⟮z⟯ ψ.comap.fieldRange = relfinrank F⟮z⟯ ⊤ := by
    have h1 : F⟮z⟯ = (F⟮z⟯).map ψ.comap := by rw [adjoin_map, Set.image_singleton, h]
    have h2 : ψ.comap.fieldRange = (⊤ : IntermediateField F E.toAffine.FunctionField).map ψ.comap :=
      (map_top_eq_fieldRange _).symm
    conv_lhs => rw [h2, h1]
    rw [relfinrank_map_map]
  have hpos : 0 < relfinrank F⟮z⟯ ⊤ := by
    rw [relfinrank_top_right]; exact Module.finrank_pos
  rw [e] at t
  have h1 : relfinrank ψ.comap.fieldRange ⊤ = 1 :=
    Nat.eq_of_mul_eq_mul_left hpos (by rw [t, mul_one])
  rw [degree, ← relfinrank_top_right]
  exact h1

theorem map_eq_app (φ : Isogeny E E') (σ : E.toAffine.FunctionField →ₐ[F] E.toAffine.FunctionField) :
    Point.map σ φ.1 = φ.app (Point.map σ (genericPoint E)) (isGenPt_map_genericPoint E σ) := by
  rw [app, ← eq_genEval E σ rfl]

theorem app_congr (φ : Isogeny E E') {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {P P' : (E.baseChange L).toAffine.Point} (h : P = P') (hP : IsGenPt E P)
    (hP' : IsGenPt E P') : φ.app P hP = φ.app P' hP' := by
  subst h; rfl

theorem app_genericPoint' (φ : Isogeny E E') : φ.app (genericPoint E) isGenPt_genericPoint = φ.1 :=
  φ.app_genericPoint _

theorem exists_map_translate (φ : Isogeny E E') (R : E.toAffine.Point) :
    ∃ c : E'.toAffine.Point,
      Point.map (translate E R) φ.1 = φ.1 + constMap E' E.toAffine.FunctionField c := by
  set G := genericPoint E
  set K := E.toAffine.FunctionField
  set α := (mulIsogeny E 2 two_ne_zero).comap
  set τ := translate E R
  set cR := constMap E K R
  have hτ : Point.map τ G = G + cR := map_translate_genericPoint E R
  have hα : Point.map α G = G + G := by
    rw [map_comap_genericPoint, ← two_zsmul]; rfl
  have hG : IsGenPt E G := isGenPt_genericPoint
  have h1 : IsGenPt E (G + cR) := hτ ▸ isGenPt_map_genericPoint E τ
  have h2 : IsGenPt E (G + G) := isGenPt_add_self hG
  have h3 : IsGenPt E (G + cR + G) := by
    have : Point.map α (G + cR) = G + cR + G := by
      rw [map_add, hα, map_constMap]; abel
    rw [← this]; exact isGenPt_map E α h1
  set Z := Point.map τ φ.1 - φ.1 with hZ
  have hτφ : Point.map τ φ.1 = φ.app (G + cR) h1 := by
    rw [map_eq_app]; exact φ.app_congr hτ _ _
  have hαZ : Point.map α Z = Z := by
    have eα : Point.map α φ.1 = φ.app (G + G) h2 := by
      rw [map_eq_app]; exact φ.app_congr hα _ _
    have eατ : Point.map α (Point.map τ φ.1) = φ.app (G + cR + G) h3 := by
      rw [Point.map_map, map_eq_app]
      refine φ.app_congr ?_ _ _
      rw [← Point.map_map, hτ, map_add, hα, map_constMap]; abel
    rw [hZ, map_sub, eα, eατ, φ.app_add h1 hG h3, φ.app_add hG hG h2, φ.app_genericPoint', hτφ]
    abel
  by_cases hZg : IsGenPt E' Z
  · exfalso
    cases hZ' : Z with
    | zero => rw [hZ'] at hZg; exact hZg
    | some z w hzw =>
      rw [hZ'] at hZg hαZ
      have hz : α z = z := by
        have := hαZ
        simp only [Point.map_some, Point.some.injEq] at this
        exact this.1
      have := (mulIsogeny E 2 two_ne_zero).degree_eq_one_of_comap_eq hZg hz
      rw [degree_mulIsogeny] at this
      norm_num at this
  · obtain ⟨c, hc⟩ := exists_map_eq_of_not_isGenPt E' Z hZg
    exact ⟨c, by rw [hc, hZ, add_sub_cancel]⟩

noncomputable def pointMap (φ : Isogeny E E') (R : E.toAffine.Point) : E'.toAffine.Point :=
  (φ.exists_map_translate R).choose

theorem map_translate (φ : Isogeny E E') (R : E.toAffine.Point) :
    Point.map (translate E R) φ.1 = φ.1 + constMap E' E.toAffine.FunctionField (φ.pointMap R) :=
  (φ.exists_map_translate R).choose_spec

theorem pointMap_eq_of_map_translate (φ : Isogeny E E') {R : E.toAffine.Point} {c : E'.toAffine.Point}
    (h : Point.map (translate E R) φ.1 = φ.1 + constMap E' E.toAffine.FunctionField c) :
    φ.pointMap R = c := by
  rw [map_translate, add_right_inj] at h
  exact constMap_injective E' _ h

theorem pointMap_add (φ : Isogeny E E') (R S : E.toAffine.Point) :
    φ.pointMap (R + S) = φ.pointMap R + φ.pointMap S := by
  apply pointMap_eq_of_map_translate
  rw [translate_add, ← Point.map_map, map_translate, map_add, map_translate, map_constMap, map_add]
  abel

noncomputable def pointHom (φ : Isogeny E E') : E.toAffine.Point →+ E'.toAffine.Point :=
  AddMonoidHom.mk' φ.pointMap φ.pointMap_add

theorem pointHom_apply (φ : Isogeny E E') (R : E.toAffine.Point) : φ.pointHom R = φ.pointMap R :=
  rfl

theorem comap_comp_translate (φ : Isogeny E E') (R : E.toAffine.Point) :
    φ.comap.comp (translate E' (φ.pointMap R)) = (translate E R).comp φ.comap := by
  apply algHom_eq_of_map_genericPoint' E'
  rw [← Point.map_map, map_translate_genericPoint, map_add, map_comap_genericPoint, ← Point.map_map,
    map_comap_genericPoint, map_translate]
  exact congrArg (φ.1 + ·) (map_constMap E' φ.comap (φ.pointMap R))

theorem app_add_constMap (φ : Isogeny E E') {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {P : (E.baseChange L).toAffine.Point} (hP : IsGenPt E P) (R : E.toAffine.Point)
    (h : IsGenPt E (P + constMap E L R)) :
    φ.app (P + constMap E L R) h = φ.app P hP + constMap E' L (φ.pointMap R) := by
  have e : genEval E (P + constMap E L R) h = (genEval E P hP).comp (translate E R) := by
    refine (eq_genEval E _ ?_ h).symm
    rw [← Point.map_map, map_translate_genericPoint, map_add, map_genEval_genericPoint]
    exact congrArg _ (map_constMap E _ R)
  rw [app, e, ← Point.map_map, map_translate, map_add, map_constMap]
  rfl

theorem translate_comap_of_mem_ker (φ : Isogeny E E') {T : E.toAffine.Point}
    (hT : T ∈ φ.pointHom.ker) (f : E'.toAffine.FunctionField) :
    translate E T (φ.comap f) = φ.comap f := by
  have := DFunLike.congr_fun (φ.comap_comp_translate T) f
  rw [AddMonoidHom.mem_ker, pointHom_apply] at hT
  rw [hT, translate_zero] at this
  exact this.symm

noncomputable def kerTranslate (φ : Isogeny E E') (T : φ.pointHom.ker) :
    E.toAffine.FunctionField →ₐ[φ.comap.fieldRange] E.toAffine.FunctionField :=
  { (translate E T).toRingHom with
    commutes' := by
      rintro ⟨m, f, rfl⟩
      exact φ.translate_comap_of_mem_ker T.2 f }

theorem kerTranslate_injective (φ : Isogeny E E') : Function.Injective φ.kerTranslate := by
  intro S T h
  exact Subtype.ext (translate_inj E (AlgHom.ext fun f => DFunLike.congr_fun h f))

theorem card_ker_le_degree (φ : Isogeny E E') : Nat.card φ.pointHom.ker ≤ φ.degree := by
  have := φ.finiteDimensional
  have hc := Nat.card_le_card_of_injective _ φ.kerTranslate_injective
  rw [Nat.card_eq_fintype_card (α := E.toAffine.FunctionField →ₐ[φ.comap.fieldRange] _)] at hc
  exact hc.trans AlgHom.card_le

instance finite_ker (φ : Isogeny E E') : Finite φ.pointHom.ker := by
  have := φ.finiteDimensional
  exact Finite.of_injective _ φ.kerTranslate_injective

theorem pointMap_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') (R : E.toAffine.Point) :
    (ψ.comp φ).pointMap R = ψ.pointMap (φ.pointMap R) := by
  apply pointMap_eq_of_map_translate
  rw [comp_val, Point.map_map, ← comap_comp_translate, ← Point.map_map, map_translate, map_add,
    map_constMap]

omit [IsAlgClosed F] in
theorem mulIsogeny_val (n : ℤ) (hn : n ≠ 0) : (mulIsogeny E n hn).1 = n • genericPoint E := rfl

theorem pointMap_mulIsogeny (n : ℤ) (hn : n ≠ 0) (R : E.toAffine.Point) :
    (mulIsogeny E n hn).pointMap R = n • R := by
  apply pointMap_eq_of_map_translate
  rw [mulIsogeny_val, map_zsmul, map_translate_genericPoint, zsmul_add, map_zsmul]
  rfl

def toHom (φ : Isogeny E E') : isogHom E E' := ⟨φ.1, φ.respectsAdd⟩

theorem toHom_val (φ : Isogeny E E') : φ.toHom.1 = φ.1 := rfl

theorem toHom_ne_zero (φ : Isogeny E E') : φ.toHom ≠ 0 :=
  fun h => isGenPt_ne_zero E' φ.isGenPt (congrArg Subtype.val h)

theorem homComp_toHom (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    homComp ψ.toHom φ.toHom = (ψ.comp φ).toHom :=
  Subtype.ext (by rw [homComp_of_isGenPt _ _ φ.isGenPt]; rfl)

end Isogeny

noncomputable def isogOfHom (Q : isogHom E E') (hQ : Q ≠ 0) : Isogeny E E' :=
  ⟨Q.1, (mem_isogHom_iff.mp Q.2).resolve_left (fun h => hQ (Subtype.ext h))⟩

theorem isogOfHom_toHom (Q : isogHom E E') (hQ : Q ≠ 0) : (isogOfHom Q hQ).toHom = Q := rfl

theorem isogOfHom_val (Q : isogHom E E') (hQ : Q ≠ 0) : (isogOfHom Q hQ).1 = Q.1 := rfl

end Points

end GroundTheory.Arith.Abelian
