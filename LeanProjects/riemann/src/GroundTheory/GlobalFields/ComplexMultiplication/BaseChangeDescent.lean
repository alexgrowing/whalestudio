import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDegree

namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section Compositum

variable {k M : Type u} [Field k] [Field M] (σ : k →+* M) (L : Type u) [Field L] [Algebra k L]

theorem exists_free_compositum :
    ∃ (L' : Type u) (_ : Field L') (ι : L →+* L') (j : M →+* L'),
      ι.comp (algebraMap k L) = j.comp σ ∧
        ∀ u : L, Transcendental k u → Transcendental j.fieldRange (ι u) := by
  classical
  letI : Algebra k M := σ.toAlgebra
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k M
  let A := MvPolynomial B L
  let L₁ := FractionRing A
  let L' := AlgebraicClosure L₁
  let toL' : A →ₐ[k] L' := IsScalarTower.toAlgHom k A L'
  have htoL' : Function.Injective toL' := by
    have h1 : Function.Injective (algebraMap A L₁) := IsFractionRing.injective A L₁
    have h2 : Function.Injective (algebraMap L₁ L') := (algebraMap L₁ L').injective
    have : (toL' : A → L') = algebraMap L₁ L' ∘ algebraMap A L₁ := by
      ext a
      simp [toL', IsScalarTower.algebraMap_apply A L₁ L']
    rw [this]
    exact h2.comp h1

  let R := Algebra.adjoin k (Set.range ((↑) : B → M))
  let e := hB.1.aevalEquiv
  let x : B → L' := fun b => toL' (MvPolynomial.X b)
  let f₀ : R →ₐ[k] L' :=
    toL'.comp ((MvPolynomial.mapAlgHom (Algebra.ofId k L)).comp e.symm.toAlgHom)
  have hf₀inj : Function.Injective f₀ := by
    refine htoL'.comp ((MvPolynomial.map_injective _ (algebraMap k L).injective).comp ?_)
    exact e.symm.injective
  have hf₀x : ∀ p : MvPolynomial B k, f₀ (e p) = MvPolynomial.aeval x p := by
    intro p
    have : toL'.comp (MvPolynomial.mapAlgHom (Algebra.ofId k L)) = MvPolynomial.aeval x := by
      apply MvPolynomial.algHom_ext
      intro b
      rw [AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X, MvPolynomial.aeval_X]
    show toL' (MvPolynomial.mapAlgHom (Algebra.ofId k L) (e.symm (e p))) = _
    rw [e.symm_apply_apply]
    exact DFunLike.congr_fun this p
  letI : Algebra R L' := f₀.toRingHom.toAlgebra
  haveI : IsScalarTower k R L' := IsScalarTower.of_algebraMap_eq (fun a => (f₀.commutes a).symm)
  haveI : Module.IsTorsionFree R L' := Module.isTorsionFree_iff_algebraMap_injective.mpr hf₀inj
  haveI : Algebra.IsAlgebraic R M := hB.isAlgebraic
  let j₀ : M →ₐ[R] L' := IsAlgClosed.lift
  let j : M →ₐ[k] L' := j₀.restrictScalars k
  let ι : L →ₐ[k] L' := IsScalarTower.toAlgHom k L L'
  refine ⟨L', inferInstance, ι.toRingHom, j.toRingHom, ?_, fun u hu => ?_⟩
  · ext a
    exact (ι.commutes a).trans (j.commutes a).symm

  have hjR : ∀ r : R, j (r : M) = f₀ r := fun r => j₀.commutes r
  have hjb : ∀ b : B, j (b : M) = x b := by
    intro b
    have hr : (b : M) = ((e (MvPolynomial.X b) : R) : M) := by
      rw [show ((e (MvPolynomial.X b) : R) : M) = MvPolynomial.aeval ((↑) : B → M) (MvPolynomial.X b)
        from hB.1.algebraMap_aevalEquiv _, MvPolynomial.aeval_X]
    rw [hr, hjR, hf₀x, MvPolynomial.aeval_X]
  have hind : AlgebraicIndependent k (Sum.elim (fun _ : Unit => ι u) x) := by
    have h1 := AlgebraicIndependent.sumElim_comp (R := k) (S := L) (A := A)
      (x := fun _ : Unit => u) (algebraicIndependent_unique_type_iff.mpr hu)
      (MvPolynomial.algebraicIndependent_X B L)
    have h2 := h1.map' htoL'
    refine (algebraicIndependent_equiv' (Equiv.sumComm Unit B) ?_).mpr h2
    funext z
    rcases z with _ | b
    · simp [ι, toL', IsScalarTower.algebraMap_apply L A L']
    · rfl
  obtain ⟨-, hu'⟩ := AlgebraicIndependent.sumElim_iff.mp hind
  have htr : Transcendental (Algebra.adjoin k (Set.range x)) (ι u) :=
    algebraicIndependent_unique_type_iff.mp hu'
  intro halg
  set R' := Algebra.adjoin k (Set.range x)
  set K₁ := j.toRingHom.fieldRange
  have hR'K : R'.toSubring ≤ K₁.toSubring := by
    show (Algebra.adjoin k (Set.range x) : Set L') ⊆ K₁
    have hle : Algebra.adjoin k (Set.range x) ≤ j.range :=
      Algebra.adjoin_le (by rintro _ ⟨b, rfl⟩; exact ⟨b, hjb b⟩)
    intro z hz
    obtain ⟨m, hm⟩ := hle hz
    exact ⟨m, hm⟩
  letI : Algebra R' K₁ := (Subring.inclusion hR'K).toAlgebra
  haveI : IsScalarTower R' K₁ L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmem : ∀ r : R, f₀ r ∈ R' := by
    intro r
    obtain ⟨p, rfl⟩ := e.surjective r
    rw [hf₀x]
    show MvPolynomial.aeval x p ∈ Algebra.adjoin k (Set.range x)
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨p, rfl⟩
  let f : R →+* R' :=
    { toFun := fun r => ⟨f₀ r, hmem r⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let g : M →+* K₁ :=
    { toFun := fun m => ⟨j m, m, rfl⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hf : Function.Injective f := fun a b h => hf₀inj (congrArg Subtype.val h)
  have hcomp : (algebraMap R' K₁).comp f = g.comp (algebraMap R M) := by
    ext r
    exact (hjR r).symm
  haveI : Algebra.IsAlgebraic R' K₁ := by
    refine ⟨fun z => ?_⟩
    obtain ⟨m, hm⟩ := z.2
    have hz : g m = z := Subtype.ext hm
    rw [← hz]
    exact (Algebra.IsAlgebraic.isAlgebraic m).ringHom_of_comp_eq f g hf hcomp
  exact htr (halg.restrictScalars R')

end Compositum

section Descent

theorem point_some_congr {K : Type*} [Field K] {W : WeierstrassCurve K} {x y x' y' : K}
    {h : W.toAffine.Nonsingular x y} {h' : W.toAffine.Nonsingular x' y'} (hx : x = x')
    (hy : y = y') : (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx hy
  rfl

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem respectsAdd_of_map (ψ : Isogeny (E.map σ) (E'.map σ))
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : Q ≠ 0)
    (hx : ffMap σ E (xOf _ Q) = ψ.x) (hy : ffMap σ E (yOf _ Q) = ψ.y) : RespectsAdd E E' Q := by
  classical
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  obtain ⟨L', _, ι, j, hcomm, htr⟩ := exists_free_compositum σ L
  letI : Algebra F' L' := j.toAlgebra
  letI : Algebra F L' := ((algebraMap F' L').comp σ).toAlgebra
  let ιA : L →ₐ[F] L' := { ι with commutes' := fun a => DFunLike.congr_fun hcomm a }
  let pm : (E.baseChange L).toAffine.Point →+ ((E.map σ).baseChange L').toAffine.Point :=
    Point.map (W' := E) ιA
  have hgen : ∀ P : (E.baseChange L).toAffine.Point, IsGenPt E P →
      IsGenPt (E.map σ) (pm P) := by
    intro P hP
    cases P with
    | zero => exact hP.elim
    | some u v h =>
      show Transcendental F' (ι u)
      intro halg
      exact htr u hP (halg.ringHom_of_comp_eq j.rangeRestrictField (RingHom.id L')
        j.rangeRestrictField.injective rfl)
  have happ : ∀ {X Y : ((E.map σ).baseChange L').toAffine.Point} (h : X = Y)
      (hX : IsGenPt (E.map σ) X) (hY : IsGenPt (E.map σ) Y), ψ.app X hX = ψ.app Y hY := by
    intro X Y h hX hY
    subst h
    rfl
  let pm' : (E'.baseChange L').toAffine.Point →+ ((E'.map σ).baseChange L').toAffine.Point :=
    AddMonoidHom.id _
  have key : ∀ (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P),
      pm' (Point.map ιA (Point.map (genEval E P hP) Q)) = ψ.app (pm P) (hgen P hP) := by
    intro P hP
    rw [Point.map_map, ← genEval_map]
    have hg : (genEval E (Point.map ιA P) (isGenPt_map E ιA hP)).toRingHom =
        (genEval (E.map σ) (pm P) (hgen P hP)).toRingHom.comp (ffMap σ E) := by
      apply ringHom_ext_functionField
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply, ffMap_algebraMap,
          AlgHom.commutes]
        rfl
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply, ffMap_genX,
          genEval_genX]
        rfl
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply, ffMap_genY,
          genEval_genY]
        rfl
    rw [Isogeny.app, ψ.val_eq]
    cases Q with
    | zero => exact absurd rfl hQ
    | some a b hab =>
      have hx' : ffMap σ E a = ψ.x := hx
      have hy' : ffMap σ E b = ψ.y := hy
      have ea : genEval E (Point.map ιA P) (isGenPt_map E ιA hP) a =
          genEval (E.map σ) (pm P) (hgen P hP) ψ.x := by
        rw [← hx']; exact DFunLike.congr_fun hg a
      have eb : genEval E (Point.map ιA P) (isGenPt_map E ιA hP) b =
          genEval (E.map σ) (pm P) (hgen P hP) ψ.y := by
        rw [← hy']; exact DFunLike.congr_fun hg b
      rw [Point.map_some]
      show (Point.some _ _ _ : ((E'.map σ).baseChange L').toAffine.Point) = Point.some _ _ _
      exact point_some_congr ea eb
  have hpm' : Function.Injective pm' := fun _ _ h => h
  apply Point.map_injective (W' := E') ιA
  apply hpm'
  rw [map_add, map_add, key _ h₃, key _ h₁, key _ h₂]
  have h₃' : IsGenPt (E.map σ) (pm P₁ + pm P₂) := by
    rw [← map_add]; exact hgen _ h₃
  rw [← ψ.app_add (hgen P₁ h₁) (hgen P₂ h₂) h₃']
  exact happ (map_add _ _ _) _ _

omit [E.IsElliptic] in

theorem transcendental_of_ffMap {z : E.toAffine.FunctionField}
    (h : Transcendental F' (ffMap σ E z)) : Transcendental F z := by
  intro halg
  refine h (halg.ringHom_of_comp_eq σ (ffMap σ E) σ.injective ?_)
  ext a
  exact (ffMap_algebraMap σ E a).symm

omit [E.IsElliptic] [E'.IsElliptic] in

theorem baseChange_map_ffMap :
    (E'.baseChange E.toAffine.FunctionField).map (ffMap σ E) =
      (E'.map σ).baseChange (E.map σ).toAffine.FunctionField := by
  have hc : (ffMap σ E).comp (algebraMap F E.toAffine.FunctionField) =
      (algebraMap F' (E.map σ).toAffine.FunctionField).comp σ := RingHom.ext (ffMap_algebraMap σ E)
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
    WeierstrassCurve.map_map, hc]

omit [E.IsElliptic] [E'.IsElliptic] in

theorem nonsingular_of_ffMap {x y : E.toAffine.FunctionField}
    (h : ((E'.map σ).baseChange (E.map σ).toAffine.FunctionField).toAffine.Nonsingular
      (ffMap σ E x) (ffMap σ E y)) :
    (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y := by
  have h' : ((E'.baseChange E.toAffine.FunctionField).map (ffMap σ E)).toAffine.Nonsingular
      (ffMap σ E x) (ffMap σ E y) := by
    rw [baseChange_map_ffMap]; exact h
  exact (WeierstrassCurve.Affine.map_nonsingular (W := (E'.baseChange _).toAffine)
    (ffMap σ E).injective x y).mp h'

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.ofMap (ψ : Isogeny (E.map σ) (E'.map σ))
    (x y : E.toAffine.FunctionField) (hx : ffMap σ E x = ψ.x) (hy : ffMap σ E y = ψ.y) :
    Isogeny E E' :=
  ⟨.some x y (nonsingular_of_ffMap σ (hx ▸ hy ▸ ψ.nonsingular)),
    (isIsogeny_iff _).mpr ⟨transcendental_of_ffMap σ (hx ▸ ψ.transcendental_alt),
      respectsAdd_of_map σ ψ (by simp) hx hy⟩⟩

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.ofMap_alt (ψ : Isogeny (E.map σ) (E'.map σ))
    (x y : E.toAffine.FunctionField) (hx : ffMap σ E x = ψ.x) (hy : ffMap σ E y = ψ.y) :
    (Isogeny.ofMap σ ψ x y hx hy).x = x := rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.ofMap_y (ψ : Isogeny (E.map σ) (E'.map σ))
    (x y : E.toAffine.FunctionField) (hx : ffMap σ E x = ψ.x) (hy : ffMap σ E y = ψ.y) :
    (Isogeny.ofMap σ ψ x y hx hy).y = y := rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_ofMap (ψ : Isogeny (E.map σ) (E'.map σ))
    (x y : E.toAffine.FunctionField) (hx : ffMap σ E x = ψ.x) (hy : ffMap σ E y = ψ.y) :
    (Isogeny.ofMap σ ψ x y hx hy).map σ = ψ :=
  Isogeny.ext_xy (by rw [Isogeny.map_x]; exact hx) (by rw [Isogeny.map_y]; exact hy)

end Descent

section Bridge

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F'] (E : WeierstrassCurve F)
  [E.IsElliptic]

theorem ffMap_algebraMap_eq_bcEmb (f : E.toAffine.FunctionField) :
    ffMap (algebraMap F F') E f = bcEmb (F' := F') E f := by
  have e : ffMap (algebraMap F F') E = (bcEmb (F' := F') E).toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      rw [ffMap_algebraMap]
      show _ = bcEmb (F' := F') E (algebraMap F _ a)
      rw [AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply F F' (E.baseChange F').toAffine.FunctionField a).symm
    · rw [ffMap_genX]; exact (bcEmb_genX E).symm
    · rw [ffMap_genY]; exact (bcEmb_genY E).symm
  exact DFunLike.congr_fun e f

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic] [DecidableEq F']

theorem isogBaseChange_alt (φ : Isogeny E E') :
    (isogBaseChange (F' := F') φ).x = bcEmb (F' := F') E φ.x := by
  show xOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem isogBaseChange_y (φ : Isogeny E E') :
    (isogBaseChange (F' := F') φ).y = bcEmb (F' := F') E φ.y := by
  show yOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

end Bridge

end GroundTheory.Global
