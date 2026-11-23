import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Differential
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialSeparable

namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

variable {F : Type u} [Field F]

section Const

variable [DecidableEq F] (E : WeierstrassCurve F) {L : Type*} [Field L] [Algebra F L] [DecidableEq L]

theorem omegaAt_constMap (R : E.toAffine.Point) : omegaAt E (constMap E L R) = 0 := by
  rcases R with _ | ⟨x, y, h⟩
  · exact omegaAt_zero E
  · refine omegaAt_some_eq E _ ?_ ?_ <;> rw [smul_zero] <;> exact (D_coeff _).symm

end Const

section Points

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem infinite_points [IsAlgClosed F] : Infinite E.toAffine.Point := by
  have key : ∀ x : F, ∃ y : F, E.toAffine.Equation x y := by
    intro x
    set q : F[X] := X ^ 2 + C (E.a₁ * x + E.a₃) * X - C (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)
    have hq : q.degree = 2 := by simp only [q]; compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hq]; decide)
    refine ⟨y, ?_⟩
    rw [equation_iff]
    simp only [q, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy
    linear_combination hy
  choose y hy using key
  refine Infinite.of_injective
    (fun x => (Point.some x (y x) (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (hy x)) :
      E.toAffine.Point)) ?_
  intro a b h
  simp only [Point.some.injEq] at h
  exact h.1

end Points

section AlgClosed

variable [IsAlgClosed F] [DecidableEq F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem translate_isogCoeff (φ : Isogeny E E') (R : E.toAffine.Point) :
    translate E R (isogCoeff φ) = isogCoeff φ := by
  have h1 := isogenyPullback_invariantDifferential_eq_smul φ
  rw [isogenyPullback_invariantDifferential] at h1
  have h2 := congrArg (kpush (translate E R)) h1
  rw [kpush_omegaAt, Isogeny.map_translate, omegaAt_add, omegaAt_constMap, add_zero, h1,
    kpush_smul, invariantDifferential, kpush_omegaAt, map_translate_genericPoint, omegaAt_add] at h2
  have h3 : omegaAt E (constPoint E R) = 0 := omegaAt_constMap E R
  rw [h3, add_zero] at h2
  exact (smul_left_injective _ (invariantDifferential_ne_zero E) h2).symm

theorem exists_isogCoeff_eq_algebraMap (φ : Isogeny E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = isogCoeff φ := by
  set K := E.toAffine.FunctionField
  set c := isogCoeff φ
  by_contra hne
  have hc : Transcendental F c := fun halg => hne (exists_algebraMap_eq_of_isAlgebraic' halg)
  have : FiniteDimensional F⟮c⟯ K := finiteDimensional_adjoin_of_transcendental E hc
  have hfix : ∀ R : E.toAffine.Point, ∀ z ∈ F⟮c⟯, translate E R z = z := by
    intro R z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact translate_isogCoeff φ R
    | algebraMap x => exact (translate E R).commutes x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  let T : E.toAffine.Point → (K →ₐ[F⟮c⟯] K) := fun R =>
    { (translate E R).toRingHom with
      commutes' := fun r => hfix R r r.2 }
  have hT : Function.Injective T := by
    intro R S h
    exact translate_inj E (AlgHom.ext fun f => DFunLike.congr_fun h f)
  have hfin : Finite E.toAffine.Point := Finite.of_injective T hT
  exact (not_finite_iff_infinite.mpr (infinite_points E)) hfin

noncomputable def isogConst (φ : Isogeny E E') : F :=
  (exists_isogCoeff_eq_algebraMap φ).choose

theorem algebraMap_isogConst (φ : Isogeny E E') :
    algebraMap F E.toAffine.FunctionField (isogConst φ) = isogCoeff φ :=
  (exists_isogCoeff_eq_algebraMap φ).choose_spec

theorem isogenyPullback_invariantDifferential_eq_const_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = isogConst φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential_eq_smul, ← algebraMap_isogConst, algebraMap_smul]

theorem isogConst_add {φ ψ χ : Isogeny E E'} (h : χ.1 = φ.1 + ψ.1) :
    isogConst χ = isogConst φ + isogConst ψ :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [map_add, algebraMap_isogConst, algebraMap_isogConst, algebraMap_isogConst, isogCoeff_add h])

variable (E) in

theorem isogConst_mulIsogeny (n : ℤ) (hn : n ≠ 0) : isogConst (mulIsogeny E n hn) = n :=
  (algebraMap F E.toAffine.FunctionField).injective (by
    rw [algebraMap_isogConst, isogCoeff_mulIsogeny, map_intCast])

theorem isSeparable_iff_isogConst_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogConst φ ≠ 0 := by
  rw [isSeparable_iff_isogCoeff_ne_zero, ← algebraMap_isogConst, ne_eq, ne_eq,
    map_eq_zero_iff _ (algebraMap F E.toAffine.FunctionField).injective]

theorem exists_homCoeff_eq_algebraMap (Q : isogHom E E') :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = homCoeff E E' Q := by
  by_cases hQ : Q = 0
  · exact ⟨0, by rw [hQ, map_zero, map_zero]⟩
  · exact exists_isogCoeff_eq_algebraMap (isogOfHom Q hQ)

variable (E E') in

noncomputable def homConst : isogHom E E' →+ F where
  toFun Q := (exists_homCoeff_eq_algebraMap Q).choose
  map_zero' := (algebraMap F E.toAffine.FunctionField).injective (by
    rw [(exists_homCoeff_eq_algebraMap (0 : isogHom E E')).choose_spec, map_zero, map_zero])
  map_add' Q₁ Q₂ := (algebraMap F E.toAffine.FunctionField).injective (by
    rw [(exists_homCoeff_eq_algebraMap (Q₁ + Q₂)).choose_spec, map_add, map_add,
      (exists_homCoeff_eq_algebraMap Q₁).choose_spec, (exists_homCoeff_eq_algebraMap Q₂).choose_spec])

theorem algebraMap_homConst (Q : isogHom E E') :
    algebraMap F E.toAffine.FunctionField (homConst E E' Q) = homCoeff E E' Q :=
  (exists_homCoeff_eq_algebraMap Q).choose_spec

theorem omegaAt_eq_homConst_smul (Q : isogHom E E') :
    omegaAt E' Q.1 = homConst E E' Q • invariantDifferential E := by
  rw [← homCoeff_smul, ← algebraMap_homConst, algebraMap_smul]

end AlgClosed

end GroundTheory.Global
