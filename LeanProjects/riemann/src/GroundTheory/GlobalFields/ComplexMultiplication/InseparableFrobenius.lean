import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialSeparable
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobeniusSep
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
import GroundTheory.ArithmeticGeometry.AbelianVarieties.SupersingularPowField

namespace GroundTheory.Global

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField GroundTheory.Arith.Abelian

universe u

section Twist

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusTwist : WeierstrassCurve F := E.map (frobenius F p)

instance [E.IsElliptic] : (frobeniusTwist E p).IsElliptic := by
  unfold frobeniusTwist; infer_instance

theorem j_frobeniusTwist [E.IsElliptic] : (frobeniusTwist E p).j = E.j ^ p := by
  show (E.map (frobenius F p)).j = _
  rw [map_j, frobenius_def]

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

theorem baseChange_frobeniusTwist :
    (frobeniusTwist E p).baseChange L = (E.baseChange L).map (frobenius L p) := by
  show (E.map (frobenius F p)).map (algebraMap F L) = (E.map (algebraMap F L)).map (frobenius L p)
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [frobenius_def]

theorem nonsingular_pow {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) := by
  rw [baseChange_frobeniusTwist]
  have := ((E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y).mpr h
  simpa only [frobenius_def] using this

theorem nonsingular_pow_iff {x y : L} :
    ((frobeniusTwist E p).baseChange L).toAffine.Nonsingular (x ^ p) (y ^ p) ↔
      (E.baseChange L).toAffine.Nonsingular x y := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_nonsingular (frobenius L p).injective x y
  simpa only [frobenius_def] using this

theorem negY_pow (x y : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.negY (x ^ p) (y ^ p) =
      (E.baseChange L).toAffine.negY x y ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_negY (frobenius L p) x y
  simpa only [frobenius_def] using this

theorem addX_pow (x₁ x₂ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addX (x₁ ^ p) (x₂ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addX x₁ x₂ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addX (frobenius L p) x₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem addY_pow (x₁ x₂ y₁ ℓ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.addY (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (ℓ ^ p) =
      (E.baseChange L).toAffine.addY x₁ x₂ y₁ ℓ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_addY (frobenius L p) x₁ y₁ x₂ ℓ
  simpa only [frobenius_def] using this

theorem slope_pow [DecidableEq L] (x₁ x₂ y₁ y₂ : L) :
    ((frobeniusTwist E p).baseChange L).toAffine.slope (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (y₂ ^ p) =
      (E.baseChange L).toAffine.slope x₁ x₂ y₁ y₂ ^ p := by
  rw [baseChange_frobeniusTwist]
  have := (E.baseChange L).toAffine.map_slope (frobenius L p) x₁ x₂ y₁ y₂
  simpa only [frobenius_def] using this

end Twist

section PointMap

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def frobeniusPoint (L : Type*) [Field L] [Algebra F L] [CharP L p] :
    (E.baseChange L).toAffine.Point → ((frobeniusTwist E p).baseChange L).toAffine.Point
  | .zero => 0
  | .some x y h => .some (x ^ p) (y ^ p) (nonsingular_pow E p h)

variable {L : Type*} [Field L] [Algebra F L] [CharP L p]

@[simp]
theorem frobeniusPoint_zero : frobeniusPoint E p L 0 = 0 := rfl

theorem frobeniusPoint_some {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    frobeniusPoint E p L (.some x y h) = .some (x ^ p) (y ^ p) (nonsingular_pow E p h) := rfl

theorem frobeniusPoint_add [DecidableEq L] (P Q : (E.baseChange L).toAffine.Point) :
    frobeniusPoint E p L (P + Q) = frobeniusPoint E p L P + frobeniusPoint E p L Q := by
  have hinj : Function.Injective fun z : L => z ^ p := by
    intro a b hab
    exact frobenius_inj L p (by simpa only [frobenius_def] using hab)
  rcases P with (_ | ⟨x₁, y₁, h₁⟩)
  · show frobeniusPoint E p L (0 + Q) = 0 + frobeniusPoint E p L Q
    rw [zero_add, zero_add]
  rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  · show frobeniusPoint E p L (Point.some x₁ y₁ h₁ + 0) = frobeniusPoint E p L (Point.some x₁ y₁ h₁) + 0
    rw [add_zero, add_zero]
  rw [frobeniusPoint_some, frobeniusPoint_some]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E.baseChange L).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, Point.add_of_Y_eq (congrArg (· ^ p) hxy.1)
      (by rw [negY_pow, hxy.2])]
    rfl
  · have hxy' : ¬(x₁ ^ p = x₂ ^ p ∧
        y₁ ^ p = ((frobeniusTwist E p).baseChange L).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
      rintro ⟨hx, hy⟩
      rw [negY_pow] at hy
      exact hxy ⟨hinj hx, hinj hy⟩
    rw [Point.add_some hxy, Point.add_some hxy', frobeniusPoint_some, Point.some.injEq,
      slope_pow, addX_pow, addY_pow]
    exact ⟨rfl, rfl⟩

theorem isGenPt_frobeniusPoint_iff (P : (E.baseChange L).toAffine.Point) :
    IsGenPt (frobeniusTwist E p) (frobeniusPoint E p L P) ↔ IsGenPt E P := by
  rcases P with (_ | ⟨x, y, h⟩)
  · exact Iff.rfl
  · rw [frobeniusPoint_some, isGenPt_some, isGenPt_some]
    exact ⟨fun ht hx => ht (hx.pow p), fun ht => ht.pow hp.out.pos⟩

end PointMap

section FrobeniusIsogeny

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] (p : ℕ) [hp : Fact p.Prime]
  [CharP F p]

omit [E.IsElliptic] in
theorem map_frobeniusPoint {L L' : Type*} [Field L] [Algebra F L] [CharP L p] [Field L']
    [Algebra F L'] [CharP L' p] [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L')
    (P : (E.baseChange L).toAffine.Point) :
    Point.map σ (frobeniusPoint E p L P) = frobeniusPoint E p L' (Point.map σ P) := by
  rcases P with (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [frobeniusPoint_some, Point.map_some, map_pow]

noncomputable def frobeniusGenPt :
    ((frobeniusTwist E p).baseChange E.toAffine.FunctionField).toAffine.Point :=
  frobeniusPoint E p _ (genericPoint E)

theorem map_genEval_frobeniusGenPt {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    Point.map (genEval E P hP) (frobeniusGenPt E p) = frobeniusPoint E p L P := by
  classical
  rw [frobeniusGenPt, map_frobeniusPoint, map_genEval_genericPoint]

theorem isGenPt_frobeniusGenPt : IsGenPt (frobeniusTwist E p) (frobeniusGenPt E p) :=
  (isGenPt_frobeniusPoint_iff E p _).mpr (transcendental_genX E)

theorem respectsAdd_frobeniusGenPt : RespectsAdd E (frobeniusTwist E p) (frobeniusGenPt E p) := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  rw [map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt, map_genEval_frobeniusGenPt,
    frobeniusPoint_add]

noncomputable def frobeniusIsogeny : Isogeny E (frobeniusTwist E p) :=
  ⟨frobeniusGenPt E p, (isIsogeny_iff _).mpr
    ⟨isGenPt_frobeniusGenPt E p, respectsAdd_frobeniusGenPt E p⟩⟩

theorem frobeniusIsogeny_app {L : Type*} [Field L] [Algebra F L] [CharP L p] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    (frobeniusIsogeny E p).app P hP = frobeniusPoint E p L P :=
  map_genEval_frobeniusGenPt E p P hP

theorem comap_frobeniusIsogeny_genX :
    (frobeniusIsogeny E p).comap (genX (frobeniusTwist E p)) = genX E ^ p :=
  (frobeniusIsogeny E p).comap_genX

theorem comap_frobeniusIsogeny_genY :
    (frobeniusIsogeny E p).comap (genY (frobeniusTwist E p)) = genY E ^ p :=
  (frobeniusIsogeny E p).comap_genY

theorem fieldRange_comap_frobeniusIsogeny :
    (frobeniusIsogeny E p).comap.fieldRange = powField E p := by
  rw [← map_top_eq_fieldRange, ← adjoin_genX_genY (frobeniusTwist E p), adjoin_map, powField]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, comap_frobeniusIsogeny_genX,
    comap_frobeniusIsogeny_genY]

theorem degree_frobeniusIsogeny [PerfectRing F p] : (frobeniusIsogeny E p).degree = p := by
  have h := congrArg (fun M : IntermediateField F E.toAffine.FunctionField =>
    Module.finrank M E.toAffine.FunctionField) (fieldRange_comap_frobeniusIsogeny E p)
  rw [Isogeny.degree]
  exact h.trans (finrank_powField E p)

end FrobeniusIsogeny

end GroundTheory.Global
