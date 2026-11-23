import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
import GroundTheory.ArithmeticGeometry.AbelianVarieties.ReductionTorsion

namespace GroundTheory.Global

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

section AlgPts

variable (E : WeierstrassCurve F) (L : Type*) {M : Type*} [Field L] [Algebra F L] [Field M]
  [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq M]

def TransOver : (E.baseChange M).toAffine.Point → Prop
  | .zero => False
  | .some x _ _ => Transcendental L x

def algPts : AddSubgroup (E.baseChange M).toAffine.Point :=
  (Point.map (W' := E) ((algebraicClosure L M).val.restrictScalars F)).range

omit [DecidableEq M] in

theorem isIntegral_y {x y : M} (h : (E.baseChange M).toAffine.Equation x y)
    (hx : x ∈ algebraicClosure L M) : y ∈ algebraicClosure L M := by
  set S := algebraicClosure L M
  have e := (equation_iff _ _).mp h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  have hc : ∀ c : F, algebraMap F M c ∈ S := fun c => by
    rw [IsScalarTower.algebraMap_apply F L M]; exact S.algebraMap_mem _
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : S, (c₁ : M) = algebraMap F M E.a₁ * x + algebraMap F M E.a₃ :=
    ⟨⟨_, S.add_mem (S.mul_mem (hc _) hx) (hc _)⟩, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : S, (c₀ : M) = x ^ 3 + algebraMap F M E.a₂ * x ^ 2 +
      algebraMap F M E.a₄ * x + algebraMap F M E.a₆ :=
    ⟨⟨_, S.add_mem (S.add_mem (S.add_mem (pow_mem hx 3)
      (S.mul_mem (hc _) (pow_mem hx 2))) (S.mul_mem (hc _) hx)) (hc _)⟩, rfl⟩
  have hy : IsIntegral S y := by
    refine ⟨X ^ 2 + C c₁ * X - C c₀, ?_, ?_⟩
    · have : (X ^ 2 + C c₁ * X - C c₀ : S[X]) = X ^ 2 + (C c₁ * X - C c₀) := by ring
      rw [this]
      exact monic_X_pow_add (by compute_degree!)
    · have key : y ^ 2 + (algebraMap F M E.a₁ * x + algebraMap F M E.a₃) * y -
          (x ^ 3 + algebraMap F M E.a₂ * x ^ 2 + algebraMap F M E.a₄ * x + algebraMap F M E.a₆) =
            0 := by linear_combination e
      simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
        IntermediateField.algebraMap_apply, hc₁, hc₀]
      exact key
  exact mem_algebraicClosure_iff'.2 (isIntegral_trans (R := L) (A := S) y hy)

theorem mem_algPts_iff_of_ne_zero {x y : M} (h : (E.baseChange M).toAffine.Nonsingular x y) :
    (Point.some x y h) ∈ algPts E L ↔ IsAlgebraic L x := by
  constructor
  · rintro ⟨P, hP⟩
    cases P with
    | zero => exact absurd hP (Point.some_ne_zero h).symm
    | some u v h' =>
      rw [Point.map_some, Point.some.injEq] at hP
      rw [← hP.1]
      exact mem_algebraicClosure_iff.1 u.2
  · intro hx
    have hx' := mem_algebraicClosure_iff.2 hx
    have hy := isIntegral_y E L h.1 hx'
    have h' : (E.baseChange (algebraicClosure L M)).toAffine.Nonsingular ⟨x, hx'⟩ ⟨y, hy⟩ :=
      (E.toAffine.baseChange_nonsingular (f := (algebraicClosure L M).val.restrictScalars F)
        (algebraicClosure L M).val.injective _ _).mp h
    exact ⟨.some _ _ h', by rw [Point.map_some]; rfl⟩

end AlgPts

section Trans

variable (E : WeierstrassCurve F) {L M : Type*} [Field L] [Algebra F L] [Field M]
  [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq L] [DecidableEq M]

variable {E} in
theorem TransOver.isGenPt {P : (E.baseChange M).toAffine.Point} (h : TransOver E L P) :
    IsGenPt E P := by
  cases P with
  | zero => exact h.elim
  | some x y _ => exact Transcendental.of_tower_top F h

theorem transOver_of_notMem {P : (E.baseChange M).toAffine.Point} (h : P ∉ algPts E L) :
    TransOver E L P := by
  cases P with
  | zero => exact h (zero_mem _)
  | some x y hxy => exact fun hx => h ((mem_algPts_iff_of_ne_zero E L hxy).2 hx)

theorem notMem_of_transOver {P : (E.baseChange M).toAffine.Point} (h : TransOver E L P) :
    P ∉ algPts E L := by
  cases P with
  | zero => exact h.elim
  | some x y hxy => exact fun hm => h ((mem_algPts_iff_of_ne_zero E L hxy).1 hm)

theorem map_mem_algPts (A : (E.baseChange L).toAffine.Point) :
    Point.map (IsScalarTower.toAlgHom F L M) A ∈ algPts E L := by
  refine ⟨Point.map ((IsScalarTower.toAlgHom L L (algebraicClosure L M)).restrictScalars F) A, ?_⟩
  rw [Point.map_map]
  congr 1

variable {E} in
theorem TransOver.add_left {B : (E.baseChange M).toAffine.Point} (hB : TransOver E L B)
    (A : (E.baseChange L).toAffine.Point) :
    TransOver E L (Point.map (IsScalarTower.toAlgHom F L M) A + B) := by
  refine transOver_of_notMem E fun hm => notMem_of_transOver E hB ?_
  have := sub_mem hm (map_mem_algPts E A)
  rwa [add_sub_cancel_left] at this

variable {E} in
theorem TransOver.neg {B : (E.baseChange M).toAffine.Point} (hB : TransOver E L B) :
    TransOver E L (-B) := by
  cases B with
  | zero => exact hB.elim
  | some x y h => exact hB

end Trans

section BaseChange

omit [Field F] in
theorem baseChange_baseChange {F : Type*} [CommRing F] (E : WeierstrassCurve F) (A B : Type*)
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B] :
    (E.baseChange A).baseChange B = E.baseChange B := by
  show E.map ((algebraMap A B).comp (algebraMap F A)) = E.map (algebraMap F B)
  rw [← IsScalarTower.algebraMap_eq]

end BaseChange

section Universal

variable (E : WeierstrassCurve F) [E.IsElliptic]

abbrev univField : Type u := (E.baseChange E.toAffine.FunctionField).toAffine.FunctionField

def univPt₁ : (E.baseChange (univField E)).toAffine.Point :=
  Point.map (IsScalarTower.toAlgHom F E.toAffine.FunctionField (univField E)) (genericPoint E)

def univPt₂ : (E.baseChange (univField E)).toAffine.Point :=
  pointCongr (baseChange_baseChange E _ _) (genericPoint (E.baseChange E.toAffine.FunctionField))

theorem isGenPt_univPt₁ : IsGenPt E (univPt₁ E) :=
  isGenPt_map E _ (transcendental_genX E)

theorem transOver_univPt₂ : TransOver E E.toAffine.FunctionField (univPt₂ E) := by
  rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
  exact transcendental_genX _

theorem isGenPt_univPt₂ : IsGenPt E (univPt₂ E) := (transOver_univPt₂ E).isGenPt

theorem isGenPt_univPt₁₂ : IsGenPt E (univPt₁ E + univPt₂ E) := by
  have := (transOver_univPt₂ E).add_left (genericPoint E)
  exact this.isGenPt

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]
  (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)

def UnivAdd : Prop :=
  Point.map (genEval E (univPt₁ E + univPt₂ E) (isGenPt_univPt₁₂ E)) Q =
    Point.map (genEval E (univPt₁ E) (isGenPt_univPt₁ E)) Q +
      Point.map (genEval E (univPt₂ E) (isGenPt_univPt₂ E)) Q

theorem map_genEval_map {L M : Type*} [Field L] [Algebra F L] [Field M] [Algebra F M]
    [DecidableEq L] [DecidableEq M] (τ : L →ₐ[F] M) {P : (E.baseChange L).toAffine.Point}
    (hP : IsGenPt E P) (hP' : IsGenPt E (Point.map τ P)) :
    Point.map (genEval E (Point.map τ P) hP') Q = Point.map τ (Point.map (genEval E P hP) Q) := by
  rw [Point.map_map, ← genEval_map E τ hP]

theorem halfUniversal (hQ : UnivAdd Q) {L M : Type*} [Field L] [Algebra F L] [Field M]
    [Algebra F M] [Algebra L M] [IsScalarTower F L M] [DecidableEq L] [DecidableEq M]
    (A : (E.baseChange L).toAffine.Point) (hA : IsGenPt E A) (B : (E.baseChange M).toAffine.Point)
    (hB : TransOver E L B) :
    Point.map (genEval E _ (hB.add_left A).isGenPt) Q =
      Point.map (genEval E _ (isGenPt_map E (IsScalarTower.toAlgHom F L M) hA)) Q +
        Point.map (genEval E B hB.isGenPt) Q := by
  set Fv := E.toAffine.FunctionField
  set σA := genEval E A hA
  letI : Algebra Fv L := σA.toRingHom.toAlgebra
  letI : Algebra Fv M := ((algebraMap L M).comp σA.toRingHom).toAlgebra
  haveI : IsScalarTower Fv L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F Fv M := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap F M c = algebraMap L M (σA (algebraMap F Fv c))
    rw [σA.commutes, ← IsScalarTower.algebraMap_apply]
  cases B with
  | zero => exact hB.elim
  | some x y h =>
  have h' : ((E.baseChange Fv).baseChange M).toAffine.Nonsingular x y := by
    rw [baseChange_baseChange]; exact h
  have hB' : IsGenPt (E.baseChange Fv) (Point.some x y h') :=
    Transcendental.restrictScalars (R := Fv) (S := L) σA.toRingHom.injective hB
  set τ₀ := genEval (E.baseChange Fv) _ hB'
  set τ : univField E →ₐ[F] M := τ₀.restrictScalars F
  have c₂ : Point.map τ (univPt₂ E) = Point.some x y h := by
    rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]
    exact ⟨genEval_genX (E.baseChange Fv) _ hB', genEval_genY (E.baseChange Fv) _ hB'⟩
  have hcomp : τ.comp (IsScalarTower.toAlgHom F Fv (univField E)) =
      (IsScalarTower.toAlgHom F L M).comp σA := by
    exact AlgHom.ext fun f => τ₀.commutes f
  have c₁ : Point.map τ (univPt₁ E) = Point.map (IsScalarTower.toAlgHom F L M) A := by
    rw [univPt₁, Point.map_map, hcomp, ← Point.map_map, map_genEval_genericPoint]
  have e := congrArg (Point.map τ) hQ
  rw [map_add, ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E))] at e
  rw [genEval_congr E (by rw [map_add, c₁, c₂]) _ (hB.add_left A).isGenPt,
    genEval_congr E c₁ _ (isGenPt_map E (IsScalarTower.toAlgHom F L M) hA),
    genEval_congr E c₂ _ hB.isGenPt] at e
  exact e

end Universal

section Criterion

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)

theorem respectsAdd_of_univAdd (hQ : UnivAdd Q) : RespectsAdd E E' Q := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  set M := (E.baseChange L).toAffine.FunctionField
  set ι := IsScalarTower.toAlgHom F L M
  set T : (E.baseChange M).toAffine.Point :=
    pointCongr (baseChange_baseChange E L M) (genericPoint (E.baseChange L))
  have hT : TransOver E L T := by
    simp only [T, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some]
    exact transcendental_genX _
  have hnT := hT.neg
  have hU := hnT.add_left P₂
  have e₁ := halfUniversal Q hQ P₁ h₁ _ hU
  have e₂ := halfUniversal Q hQ P₂ h₂ _ hnT
  have e₃ := halfUniversal Q hQ (P₁ + P₂) h₃ _ hnT
  have hsum : Point.map ι P₁ + (Point.map ι P₂ + -T) = Point.map ι (P₁ + P₂) + -T := by
    rw [map_add, add_assoc]
  rw [genEval_congr E hsum _ (hnT.add_left (P₁ + P₂)).isGenPt, e₃, e₂] at e₁
  have key : Point.map (genEval E _ (isGenPt_map E ι h₃)) Q =
      Point.map (genEval E _ (isGenPt_map E ι h₁)) Q +
        Point.map (genEval E _ (isGenPt_map E ι h₂)) Q := by
    have := congrArg (· - Point.map (genEval E (-T) hnT.isGenPt) Q) e₁
    simp only [add_sub_cancel_right] at this
    rw [this]
    abel
  rw [map_genEval_map Q ι h₃, map_genEval_map Q ι h₁, map_genEval_map Q ι h₂, ← map_add] at key
  exact Point.map_injective ι key

end Criterion

end

end GroundTheory.Global
