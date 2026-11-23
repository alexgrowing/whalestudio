import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField
import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
import GroundTheory.GlobalFields.ComplexMultiplication.TorsionReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section Translate

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem isGenPt_genericPoint_add_constMap (R : E.toAffine.Point) :
    IsGenPt E (genericPoint E + constMap E E.toAffine.FunctionField R) := by
  have hG : TransOver E F (genericPoint E) := transcendental_genX E
  have := hG.add_left (M := E.toAffine.FunctionField) R
  rw [add_comm]
  exact this.isGenPt

end Translate

section OverF

variable {F : Type u} [Field F] [DecidableEq F] {E E' : WeierstrassCurve F} [E.IsElliptic]
  [E'.IsElliptic] (Ω : Type u) [Field Ω] [Algebra F Ω] [DecidableEq Ω]

omit [DecidableEq F] in

theorem isogBaseChange_app (φ : Isogeny E E')
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (hX : IsGenPt (E.baseChange Ω) X)
    (hX' : IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)) :
    (isogBaseChange (F' := Ω) φ).app X hX =
      φ.app (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) hX' := by
  have hg : ((genEval (E.baseChange Ω) X hX).restrictScalars F).comp (bcEmb (F' := Ω) E) =
      genEval E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
        hX' := by
    refine eq_genEval E _ ?_ _
    cases X with
    | zero => exact hX.elim
    | some u v hv =>
      simp only [GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
      congr 1
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genX E)) = u
        rw [bcEmb_genX]; exact genEval_genX (E.baseChange Ω) _ hX
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genY E)) = v
        rw [bcEmb_genY]; exact genEval_genY (E.baseChange Ω) _ hX
  unfold Isogeny.app
  rw [isogBaseChange_val, ← hg, ← Point.map_map]
  generalize Point.map (W' := E') (bcEmb (F' := Ω) E) φ.1 = Y
  cases Y <;> rfl

omit [DecidableEq F] [E.IsElliptic] [DecidableEq Ω] in

theorem isGenPt_of_isGenPt_baseChange
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (h : IsGenPt (E.baseChange Ω) X) :
    IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) := by
  cases X with
  | zero => exact h.elim
  | some x y _ => exact Transcendental.restrictScalars (algebraMap F Ω).injective h

omit [E.IsElliptic] in

theorem constMap_constMap_baseChange (V : WeierstrassCurve F) (R : V.toAffine.Point) :
    (constMap (V.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField (constMap V Ω R) :
      (V.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) =
      constMap V (E.baseChange Ω).toAffine.FunctionField R := by
  cases R <;> rfl

theorem app_genericPoint_add_constMap [PerfectField F] [IsAlgClosed Ω] (φ : Isogeny E E')
    (R : E.toAffine.Point) :
    φ.app (genericPoint E + constMap E E.toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap E R) =
      φ.1 + constMap E' E.toAffine.FunctionField (pointHomOver Ω φ R) := by
  set K' := (E.baseChange Ω).toAffine.FunctionField
  set ι := bcEmb (F' := Ω) E
  set Rω := constMap E Ω R
  set φΩ := isogBaseChange (F' := Ω) φ
  have hGΩ : IsGenPt (E.baseChange Ω) (genericPoint (E.baseChange Ω)) :=
    transcendental_genX (E.baseChange Ω)
  have hX := isGenPt_genericPoint_add_constMap (E.baseChange Ω) Rω
  have h1 := φΩ.app_add_constMap hGΩ Rω hX
  rw [φΩ.app_genericPoint hGΩ, ← constMap_pointHomOver] at h1
  have app_eq : ∀ {P P' : (E.baseChange K').toAffine.Point} (h : P = P') (hP : IsGenPt E P)
      (hP' : IsGenPt E P'), φ.app P hP = φ.app P' hP' := by
    intro P P' h hP hP'; subst h; rfl
  have e1 : Point.map ι (genericPoint E + constMap E E.toAffine.FunctionField R) =
      ((genericPoint (E.baseChange Ω) + constMap (E.baseChange Ω) K' Rω :
        ((E.baseChange Ω).baseChange K').toAffine.Point) : (E.baseChange K').toAffine.Point) := by
    rw [map_add, map_bcEmb_genericPoint, map_constMap, ← constMap_constMap_baseChange Ω E R]
    rfl
  have hX' := isGenPt_of_isGenPt_baseChange Ω _ hX
  apply Point.map_injective (W' := E') ι
  rw [Isogeny.map_app]
  refine (app_eq e1 _ hX').trans ?_
  rw [← isogBaseChange_app Ω φ _ hX hX', h1, map_add, map_constMap,
    ← constMap_constMap_baseChange Ω (E := E) E' (pointHomOver Ω φ R)]
  rfl

end OverF

section Reduction

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem reduceFF_constMap (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (c : (V.baseChange K).toAffine.Point) :
    reduceFF K W V (constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField c) =
      constMap (V.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
        (reducePoint K V c) := by
  have hσ : (algebraMap K (W.baseChange K).toAffine.FunctionField).comp (algebraMap 𝒪 K) =
      (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp
        (algebraMap 𝒪 (gaussRing W)) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  cases c with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | some X Y h =>
    by_cases hX : X ∈ Set.range (algebraMap 𝒪 K)
    · obtain ⟨x, rfl⟩ := hX
      obtain ⟨y, rfl⟩ := exists_y_of_equation K V h.1
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some _ _ h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField
            (algebraMap 𝒪 K x)) (algebraMap K (W.baseChange K).toAffine.FunctionField
              (algebraMap 𝒪 K y)) h₁ := ⟨_, rfl⟩
      have hx := RingHom.congr_fun hσ x
      have hy := RingHom.congr_fun hσ y
      simp only [RingHom.comp_apply] at hx hy
      obtain ⟨h₂, e₂⟩ := exists_some_eq h₁ hx hy
      obtain ⟨h₃, e₃⟩ := reduceFF_some K W V h₂
      rw [e₁, e₂, e₃]
      have e₄ := reducePoint_some_integral K V h (nonsingular_residue_of_isElliptic K V h.1)
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      show _ = Point.some _ _ _
      simp only [Point.some.injEq, gaussResidue_residue_algebraMap]
      exact ⟨rfl, rfl⟩
    · have hX' := map_notMem_range K (W.baseChange K).toAffine.FunctionField
        (f := algebraMap 𝒪 (gaussRing W)) hσ hX
      have e₄ := reducePoint_some_notMem K V h hX
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some X Y h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField X)
            (algebraMap K (W.baseChange K).toAffine.FunctionField Y) h₁ := ⟨_, rfl⟩
      rw [e₁, map_zero]
      simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        reductionHom_apply]
      rw [pointCongr_some, reducePoint_some_notMem _ (gaussCurve W V) _ hX', map_zero, map_zero]

variable [W.IsElliptic] [W'.IsElliptic]

theorem reduceFF_genericPoint_add_constMap (R : (W.baseChange K).toAffine.Point) :
    reduceFF K W W (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R) =
      genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R) := by
  rw [map_add, reduceFF_genericPoint, reduceFF_constMap]

set_option maxHeartbeats 1000000 in

theorem reduceIsogeny_app_add_constMap (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) (S : (W'.baseChange K).toAffine.Point)
    (h : φ.app (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap _ R) =
      φ.1 + constMap (W'.baseChange K) (W.baseChange K).toAffine.FunctionField S) :
    (reduceIsogeny K W W' φ).app (genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R)) (isGenPt_genericPoint_add_constMap _ _) =
      (reduceIsogeny K W W' φ).1 + constMap (W'.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField (reducePoint K W' S) := by
  have hR' : IsGenPt (W.map (residue 𝒪)) (reduceFF K W W (genericPoint (W.baseChange K) +
      constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)) := by
    rw [reduceFF_genericPoint_add_constMap]
    exact isGenPt_genericPoint_add_constMap _ _
  have key := reduceFF_map_genEval K W W W' (isGenPt_genericPoint_add_constMap _ R) hR' φ.1
  have h2 := congrArg (reduceFF K W W') h
  rw [map_add, reduceFF_constMap] at h2
  rw [reduceIsogeny_val, ← h2]
  unfold Isogeny.app at key ⊢
  rw [key, reduceIsogeny_val, genEval_congr _ (reduceFF_genericPoint_add_constMap K W R) hR']

end Reduction

section PointsOverPerfect

universe v w

variable {𝒪 : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type v) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [PerfectField K] [PerfectField (ResidueField 𝒪)]
  (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
  (Ωk : Type w) [Field Ωk] [Algebra (ResidueField 𝒪) Ωk] [IsAlgClosed Ωk] [DecidableEq Ωk]

theorem reducePoint_pointHomOver (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) :
    reducePoint K W' (pointHomOver Ω φ R) =
      pointHomOver Ωk (reduceIsogeny K W W' φ) (reducePoint K W R) := by
  have h := reduceIsogeny_app_add_constMap K W W' φ R _ (app_genericPoint_add_constMap Ω φ R)
  rw [app_genericPoint_add_constMap Ωk (reduceIsogeny K W W' φ) (reducePoint K W R),
    add_right_inj] at h
  exact (constMap_injective _ _ h).symm

end PointsOverPerfect

end

end GroundTheory.Global
