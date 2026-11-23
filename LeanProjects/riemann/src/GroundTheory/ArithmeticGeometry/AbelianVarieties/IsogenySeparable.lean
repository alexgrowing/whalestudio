import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E E' : WeierstrassCurve F}
  [E.IsElliptic] [E'.IsElliptic]

namespace Isogeny

theorem exists_ker_of_algHom (φ : Isogeny E E')
    (σ : E.toAffine.FunctionField →ₐ[φ.comap.fieldRange]
      AlgebraicClosure E.toAffine.FunctionField) :
    ∃ T : E.toAffine.Point, T ∈ φ.pointHom.ker ∧ σ.restrictScalars F =
      (IsScalarTower.toAlgHom F E.toAffine.FunctionField
        (AlgebraicClosure E.toAffine.FunctionField)).comp (translate E T) := by
  classical
  set K := E.toAffine.FunctionField
  set Ω := AlgebraicClosure K
  set ι := IsScalarTower.toAlgHom F K Ω
  set σF := σ.restrictScalars F
  have hσφ : σF.comp φ.comap = ι.comp φ.comap := by
    refine AlgHom.ext fun f => ?_
    have := σ.commutes ⟨φ.comap f, f, rfl⟩
    simp only [AlgHom.comp_apply]
    exact this
  set G := genericPoint E
  have hσg : IsGenPt E (Point.map σF G) := isGenPt_map_genericPoint E σF
  have hιg : IsGenPt E (Point.map ι G) := isGenPt_map_genericPoint E ι
  have happ : φ.app _ hσg = φ.app _ hιg := by
    rw [φ.app_eq_map_comp, φ.app_eq_map_comp, ← eq_genEval E σF rfl hσg,
      ← eq_genEval E ι rfl hιg, hσφ]
  set Z := Point.map σF G - Point.map ι G with hZ
  have hsum : Point.map ι G + Z = Point.map σF G := by rw [hZ]; abel
  by_cases hZg : IsGenPt E Z
  · exfalso
    have e := φ.app_add hιg hZg (hsum ▸ hσg)
    rw [φ.app_congr hsum _ hσg, happ, left_eq_add] at e
    exact isGenPt_ne_zero E' (φ.isGenPt_app Z hZg) e
  · obtain ⟨T, hT⟩ := exists_map_eq_of_not_isGenPt E Z hZg
    rw [← hT] at hsum
    have key := φ.app_add_constMap hιg T (hsum ▸ hσg)
    rw [φ.app_congr hsum _ hσg, happ, left_eq_add] at key
    have hker : φ.pointMap T = 0 :=
      constMap_injective E' Ω (by rw [key, map_zero])
    refine ⟨T, hker, ?_⟩
    apply algHom_eq_of_map_genericPoint' E
    rw [← hsum, ← Point.map_map, map_translate_genericPoint, map_add]
    exact congrArg _ (map_constMap E ι T).symm

theorem finSepDegree_le_card_ker (φ : Isogeny E E') :
    Field.finSepDegree φ.comap.fieldRange E.toAffine.FunctionField ≤ Nat.card φ.pointHom.ker := by
  classical
  let f : Field.Emb φ.comap.fieldRange E.toAffine.FunctionField → φ.pointHom.ker := fun σ =>
    ⟨(φ.exists_ker_of_algHom σ).choose, (φ.exists_ker_of_algHom σ).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have e1 := (φ.exists_ker_of_algHom σ).choose_spec.2
    have e2 := (φ.exists_ker_of_algHom τ).choose_spec.2
    have hT : (φ.exists_ker_of_algHom σ).choose = (φ.exists_ker_of_algHom τ).choose :=
      congrArg Subtype.val h
    apply AlgHom.restrictScalars_injective F
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [hT]
  exact Nat.card_le_card_of_injective f hf

noncomputable def kerAut (φ : Isogeny E E') (T : φ.pointHom.ker) :
    E.toAffine.FunctionField ≃ₐ[φ.comap.fieldRange] E.toAffine.FunctionField :=
  AlgEquiv.ofAlgHom (φ.kerTranslate T) (φ.kerTranslate (-T))
    (AlgHom.ext fun f => translate_translate_neg E T f)
    (AlgHom.ext fun f => by
      have := translate_translate_neg E (-(T : E.toAffine.Point)) f
      rw [neg_neg] at this
      exact this)

theorem kerAut_apply (φ : Isogeny E E') (T : φ.pointHom.ker) (f : E.toAffine.FunctionField) :
    φ.kerAut T f = translate E T f := rfl

noncomputable def kerAutHom (φ : Isogeny E E') :
    Multiplicative φ.pointHom.ker →*
      (E.toAffine.FunctionField ≃ₐ[φ.comap.fieldRange] E.toAffine.FunctionField) where
  toFun T := φ.kerAut T.toAdd
  map_one' := AlgEquiv.ext fun f => by
    rw [kerAut_apply]
    exact DFunLike.congr_fun (translate_zero E) f
  map_mul' S T := AlgEquiv.ext fun f => by
    rw [AlgEquiv.mul_apply, kerAut_apply, kerAut_apply, kerAut_apply, toAdd_mul,
      AddSubgroup.coe_add, translate_translate]

theorem kerAutHom_injective (φ : Isogeny E E') : Function.Injective φ.kerAutHom := by
  intro S T h
  have := φ.kerTranslate_injective (a₁ := S.toAdd) (a₂ := T.toAdd)
    (AlgHom.ext fun f => DFunLike.congr_fun h f)
  exact this

noncomputable def fixedKer (φ : Isogeny E E') :
    IntermediateField φ.comap.fieldRange E.toAffine.FunctionField :=
  fixedField φ.kerAutHom.range

theorem mem_fixedKer_of_forall (φ : Isogeny E E') {g : E.toAffine.FunctionField}
    (h : ∀ T ∈ φ.pointHom.ker, translate E T g = g) : g ∈ φ.fixedKer := by
  rw [fixedKer, mem_fixedField_iff]
  rintro _ ⟨T, rfl⟩
  exact h _ T.toAdd.2

theorem card_kerAutHom_range (φ : Isogeny E E') :
    Nat.card φ.kerAutHom.range = Nat.card φ.pointHom.ker := by
  rw [← Nat.card_congr (MonoidHom.ofInjective φ.kerAutHom_injective).toEquiv]
  rfl

theorem finrank_fixedKer (φ : Isogeny E E') :
    Module.finrank φ.fixedKer E.toAffine.FunctionField = Nat.card φ.pointHom.ker := by
  have := φ.finiteDimensional
  rw [fixedKer, finrank_fixedField_eq_card, card_kerAutHom_range]

theorem card_ker_le_finSepDegree_fixedKer (φ : Isogeny E E') :
    Nat.card φ.pointHom.ker ≤ Field.finSepDegree φ.fixedKer E.toAffine.FunctionField := by
  have := φ.finiteDimensional
  rw [← card_kerAutHom_range]
  let ι := IsScalarTower.toAlgHom φ.fixedKer E.toAffine.FunctionField
    (AlgebraicClosure E.toAffine.FunctionField)
  let f : φ.kerAutHom.range → Field.Emb φ.fixedKer E.toAffine.FunctionField := fun h =>
    ι.comp { (h.1 : E.toAffine.FunctionField ≃ₐ[φ.comap.fieldRange] _).toRingHom with
      commutes' := fun x => (mem_fixedField_iff _ _).mp x.2 h.1 h.2 }
  have hf : Function.Injective f := by
    intro h₁ h₂ e
    refine Subtype.ext (AlgEquiv.ext fun x => ι.toRingHom.injective ?_)
    exact DFunLike.congr_fun e x
  exact Nat.card_le_card_of_injective f hf

theorem finSepDegree_fixedKer (φ : Isogeny E E') :
    Field.finSepDegree φ.comap.fieldRange φ.fixedKer = 1 := by
  have := φ.finiteDimensional
  have hmul := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic φ.comap.fieldRange φ.fixedKer
    E.toAffine.FunctionField
  have h1 := φ.finSepDegree_le_card_ker
  have h2 := φ.card_ker_le_finSepDegree_fixedKer
  have h3 : 0 < Field.finSepDegree φ.fixedKer E.toAffine.FunctionField :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  have h4 : 0 < Field.finSepDegree φ.comap.fieldRange φ.fixedKer := Nat.pos_of_ne_zero (NeZero.ne _)
  have : Field.finSepDegree φ.comap.fieldRange φ.fixedKer *
      Field.finSepDegree φ.fixedKer E.toAffine.FunctionField ≤
      1 * Field.finSepDegree φ.fixedKer E.toAffine.FunctionField := by
    rw [hmul, one_mul]; exact h1.trans h2
  have := Nat.le_of_mul_le_mul_right this h3
  omega

instance isPurelyInseparable_fixedKer (φ : Isogeny E E') :
    IsPurelyInseparable φ.comap.fieldRange φ.fixedKer :=
  isPurelyInseparable_of_finSepDegree_eq_one φ.finSepDegree_fixedKer

noncomputable def insepDeg (φ : Isogeny E E') : ℕ :=
  Module.finrank φ.comap.fieldRange φ.fixedKer

theorem degree_eq_insepDeg_mul (φ : Isogeny E E') :
    φ.degree = φ.insepDeg * Nat.card φ.pointHom.ker := by
  haveI : Module.Free φ.comap.fieldRange φ.fixedKer := Module.Free.of_divisionRing _ _
  haveI : Module.Free φ.fixedKer E.toAffine.FunctionField := Module.Free.of_divisionRing _ _
  rw [degree, insepDeg, ← finrank_fixedKer, Module.finrank_mul_finrank]

theorem insepDeg_pos (φ : Isogeny E E') : 0 < φ.insepDeg := by
  have := φ.finiteDimensional
  exact Module.finrank_pos

theorem exists_insepDeg_eq_pow (φ : Isogeny E E') : ∃ n, φ.insepDeg = ringExpChar F ^ n := by
  have := φ.finiteDimensional
  have : ExpChar φ.comap.fieldRange (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F φ.comap.fieldRange).injective (ringExpChar F)
  exact IsPurelyInseparable.finrank_eq_pow φ.comap.fieldRange φ.fixedKer (ringExpChar F)

theorem exists_comap_eq_pow (φ : Isogeny E E') {a : E.toAffine.FunctionField} (ha : a ∈ φ.fixedKer) :
    ∃ f : E'.toAffine.FunctionField, φ.comap f = a ^ φ.insepDeg := by
  have := φ.finiteDimensional
  set x : φ.fixedKer := ⟨a, ha⟩
  obtain ⟨n, y, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C φ.comap.fieldRange
    (ringExpChar φ.comap.fieldRange) x
  have hint : IsIntegral φ.comap.fieldRange x := Algebra.IsIntegral.isIntegral x
  have hdvd := minpoly.degree_dvd hint
  rw [hmin, natDegree_sub_C, natDegree_X_pow] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hroot := minpoly.aeval φ.comap.fieldRange x
  rw [hmin, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at hroot
  obtain ⟨f, hf⟩ := (y ^ c).2
  refine ⟨f, ?_⟩
  have : x ^ φ.insepDeg = algebraMap φ.comap.fieldRange φ.fixedKer (y ^ c) := by
    rw [insepDeg, hc, pow_mul, hroot, map_pow]
  have := congrArg (fun z : φ.fixedKer => (z : E.toAffine.FunctionField)) this
  simp only [SubmonoidClass.coe_pow] at this
  have hf' : φ.comap f = ((y ^ c : φ.comap.fieldRange) : E.toAffine.FunctionField) := hf
  rw [hf']
  exact this.symm

end Isogeny

end GroundTheory.Arith.Abelian
