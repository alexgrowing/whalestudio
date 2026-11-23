import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F]

section GenPt

variable (E : WeierstrassCurve F)

def IsGenPt {L : Type*} [Field L] [Algebra F L] : (E.baseChange L).toAffine.Point → Prop
  | .zero => False
  | .some x _ _ => Transcendental F x

noncomputable def genEval {L : Type*} [Field L] [Algebra F L] :
    (P : (E.baseChange L).toAffine.Point) → IsGenPt E P → (E.toAffine.FunctionField →ₐ[F] L)
  | .zero, h => h.elim
  | .some _ _ h, ht => liftPoint E h.1 ht

theorem isGenPt_some {L : Type*} [Field L] [Algebra F L] {x y : L}
    (h : (E.baseChange L).toAffine.Nonsingular x y) :
    IsGenPt E (.some x y h) ↔ Transcendental F x := Iff.rfl

theorem genEval_congr {L : Type*} [Field L] [Algebra F L] {P P' : (E.baseChange L).toAffine.Point}
    (h : P = P') (hP : IsGenPt E P) (hP' : IsGenPt E P') : genEval E P hP = genEval E P' hP' := by
  subst h; rfl

theorem isGenPt_ne_zero {L : Type*} [Field L] [Algebra F L] {P : (E.baseChange L).toAffine.Point}
    (hP : IsGenPt E P) : P ≠ 0 := by
  rintro rfl; exact hP

theorem genEval_genX {L : Type*} [Field L] [Algebra F L] (P : (E.baseChange L).toAffine.Point)
    (hP : IsGenPt E P) : genEval E P hP (genX E) = xOf _ P := by
  cases P with
  | zero => exact hP.elim
  | some x y h => exact liftPoint_genX E h.1 hP

theorem genEval_genY {L : Type*} [Field L] [Algebra F L] (P : (E.baseChange L).toAffine.Point)
    (hP : IsGenPt E P) : genEval E P hP (genY E) = yOf _ P := by
  cases P with
  | zero => exact hP.elim
  | some x y h => exact liftPoint_genY E h.1 hP

variable [E.IsElliptic]

theorem map_genEval_genericPoint {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    Point.map (genEval E P hP) (genericPoint E) = P := by
  cases P with
  | zero => exact hP.elim
  | some x y h => exact map_liftPoint_genericPoint E h hP

theorem isGenPt_map_genericPoint {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (σ : E.toAffine.FunctionField →ₐ[F] L) : IsGenPt E (Point.map σ (genericPoint E)) := by
  show Transcendental F (σ (genX E))
  exact fun h => transcendental_genX E ((isAlgebraic_algHom_iff σ σ.toRingHom.injective).mp h)

theorem eq_genEval {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (σ : E.toAffine.FunctionField →ₐ[F] L) {P : (E.baseChange L).toAffine.Point}
    (h : Point.map σ (genericPoint E) = P) (hP : IsGenPt E P) : σ = genEval E P hP := by
  subst h
  apply algHom_ext_gen E
  · rw [genEval_genX]; rfl
  · rw [genEval_genY]; rfl

theorem algHom_eq_of_map_genericPoint' {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {σ τ : E.toAffine.FunctionField →ₐ[F] L}
    (h : Point.map σ (genericPoint E) = Point.map τ (genericPoint E)) : σ = τ := by
  rw [eq_genEval E σ rfl (isGenPt_map_genericPoint E σ), eq_genEval E τ h.symm
    (isGenPt_map_genericPoint E σ)]

theorem isGenPt_map {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L']
    [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L') {P : (E.baseChange L).toAffine.Point}
    (hP : IsGenPt E P) : IsGenPt E (Point.map σ P) := by
  rw [← map_genEval_genericPoint E P hP, Point.map_map]
  exact isGenPt_map_genericPoint E _

theorem genEval_map {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L']
    [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L') {P : (E.baseChange L).toAffine.Point}
    (hP : IsGenPt E P) :
    genEval E (Point.map σ P) (isGenPt_map E σ hP) = σ.comp (genEval E P hP) :=
  (eq_genEval E _ (by rw [← Point.map_map, map_genEval_genericPoint]) _).symm

end GenPt

section App

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem isIsogeny_iff (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) :
    IsIsogeny E E' Q ↔ IsGenPt E' Q ∧ RespectsAdd E E' Q := by
  constructor
  · rintro ⟨⟨x, y, h, rfl, hx⟩, hr⟩
    exact ⟨hx, hr⟩
  · rintro ⟨hg, hr⟩
    cases Q with
    | zero => exact hg.elim
    | some x y h => exact ⟨⟨x, y, h, rfl, hg⟩, hr⟩

omit [E.IsElliptic] [E'.IsElliptic] in

theorem respectsAdd_iff (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) :
    RespectsAdd E E' Q ↔ ∀ (L : Type u) [Field L] [Algebra F L] [DecidableEq L]
      (P₁ P₂ : (E.baseChange L).toAffine.Point) (h₁ : IsGenPt E P₁) (h₂ : IsGenPt E P₂)
      (h₃ : IsGenPt E (P₁ + P₂)), Point.map (genEval E (P₁ + P₂) h₃) Q =
        Point.map (genEval E P₁ h₁) Q + Point.map (genEval E P₂ h₂) Q := by
  constructor
  · intro hQ L _ _ _ P₁ P₂ h₁ h₂ h₃
    cases P₁ with
    | zero => exact h₁.elim
    | some u₁ v₁ k₁ =>
      cases P₂ with
      | zero => exact h₂.elim
      | some u₂ v₂ k₂ =>
        generalize hs : Point.some u₁ v₁ k₁ + Point.some u₂ v₂ k₂ = P₃ at h₃ ⊢
        cases P₃ with
        | zero => exact h₃.elim
        | some u₃ v₃ k₃ => exact hQ L u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ h₁ h₂ h₃ hs
  · intro hQ L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ t₁ t₂ t₃ hs
    have key := hQ L (.some u₁ v₁ k₁) (.some u₂ v₂ k₂) t₁ t₂ (hs ▸ t₃)
    rw [genEval_congr E hs _ t₃] at key
    exact key

omit [E.IsElliptic] [E'.IsElliptic] in
theorem respectsAdd_zero : RespectsAdd E E' 0 := by
  intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ t₁ t₂ t₃ _
  simp only [ratMapValue, map_zero, add_zero]

omit [E.IsElliptic] [E'.IsElliptic] in
theorem RespectsAdd.add {Q₁ Q₂ : (E'.baseChange E.toAffine.FunctionField).toAffine.Point}
    (h₁ : RespectsAdd E E' Q₁) (h₂ : RespectsAdd E E' Q₂) : RespectsAdd E E' (Q₁ + Q₂) := by
  intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ t₁ t₂ t₃ hs
  have e₁ := h₁ L u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ t₁ t₂ t₃ hs
  have e₂ := h₂ L u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ t₁ t₂ t₃ hs
  simp only [ratMapValue, map_add] at e₁ e₂ ⊢
  rw [e₁, e₂]
  abel

omit [E.IsElliptic] [E'.IsElliptic] in
theorem RespectsAdd.neg {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point}
    (h : RespectsAdd E E' Q) : RespectsAdd E E' (-Q) := by
  intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ t₁ t₂ t₃ hs
  have e := h L u₁ v₁ u₂ v₂ u₃ v₃ k₁ k₂ k₃ t₁ t₂ t₃ hs
  simp only [ratMapValue, map_neg] at e ⊢
  rw [e, neg_add]

variable (E E') in

def isogHom : AddSubgroup (E'.baseChange E.toAffine.FunctionField).toAffine.Point where
  carrier := {Q | RespectsAdd E E' Q}
  zero_mem' := respectsAdd_zero
  add_mem' := RespectsAdd.add
  neg_mem' := RespectsAdd.neg

theorem respectsAdd_genericPoint : RespectsAdd E E (genericPoint E) := by
  rw [respectsAdd_iff]
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  rw [map_genEval_genericPoint, map_genEval_genericPoint, map_genEval_genericPoint]

namespace Isogeny

theorem ext' {φ ψ : Isogeny E E'} (h : φ.1 = ψ.1) : φ = ψ := Subtype.ext h

theorem isGenPt (φ : Isogeny E E') : IsGenPt E' φ.1 := ((isIsogeny_iff _).mp φ.2).1

theorem respectsAdd (φ : Isogeny E E') : RespectsAdd E E' φ.1 := φ.2.2

theorem map_comap_genericPoint (φ : Isogeny E E') :
    Point.map φ.comap (genericPoint E') = φ.1 := by
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  rw [comap, map_liftPoint_genericPoint E' φ.nonsingular φ.transcendental_alt]
  simp only [he, Isogeny.x, Isogeny.y]
  rfl

theorem comap_eq_genEval (φ : Isogeny E E') : φ.comap = genEval E' φ.1 φ.isGenPt :=
  eq_genEval E' φ.comap φ.map_comap_genericPoint φ.isGenPt

noncomputable def app (φ : Isogeny E E') {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    (E'.baseChange L).toAffine.Point :=
  Point.map (genEval E P hP) φ.1

theorem app_eq_map_comp (φ : Isogeny E E') {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    φ.app P hP = Point.map ((genEval E P hP).comp φ.comap) (genericPoint E') := by
  rw [app, ← Point.map_map, map_comap_genericPoint]

theorem isGenPt_app (φ : Isogeny E E') {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) : IsGenPt E' (φ.app P hP) := by
  rw [app_eq_map_comp]; exact isGenPt_map_genericPoint E' _

theorem genEval_app (φ : Isogeny E E') {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    genEval E' (φ.app P hP) (φ.isGenPt_app P hP) = (genEval E P hP).comp φ.comap :=
  (eq_genEval E' _ (φ.app_eq_map_comp P hP).symm _).symm

theorem app_genericPoint (φ : Isogeny E E') (h : IsGenPt E (genericPoint E)) :
    φ.app (genericPoint E) h = φ.1 := by
  rw [app, ← eq_genEval E (AlgHom.id F _) (by cases genericPoint E <;> rfl) h]
  cases φ.1 <;> rfl

theorem app_add (φ : Isogeny E E') {L : Type u} [Field L] [Algebra F L] [DecidableEq L]
    {P₁ P₂ : (E.baseChange L).toAffine.Point} (h₁ : IsGenPt E P₁) (h₂ : IsGenPt E P₂)
    (h₃ : IsGenPt E (P₁ + P₂)) : φ.app (P₁ + P₂) h₃ = φ.app P₁ h₁ + φ.app P₂ h₂ :=
  (respectsAdd_iff _).mp φ.respectsAdd L P₁ P₂ h₁ h₂ h₃

theorem map_app (φ : Isogeny E E') {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L']
    [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L') (P : (E.baseChange L).toAffine.Point)
    (hP : IsGenPt E P) : Point.map σ (φ.app P hP) = φ.app (Point.map σ P) (isGenPt_map E σ hP) := by
  rw [app, app, Point.map_map, genEval_map]

noncomputable def comp (ψ : Isogeny E' E'') (φ : Isogeny E E') : Isogeny E E'' :=
  ⟨ψ.app φ.1 φ.isGenPt, (isIsogeny_iff _).mpr ⟨ψ.isGenPt_app _ _, by
    rw [respectsAdd_iff]
    intro L _ _ _ P₁ P₂ h₁ h₂ h₃
    have key : ∀ (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P),
        Point.map (genEval E P hP) (ψ.app φ.1 φ.isGenPt) = ψ.app (φ.app P hP) (φ.isGenPt_app P hP) := by
      intro P hP
      rw [map_app]
      rfl
    rw [key, key, key]
    have e := φ.app_add h₁ h₂ h₃
    have h₃' : IsGenPt E' (φ.app P₁ h₁ + φ.app P₂ h₂) := e ▸ φ.isGenPt_app _ h₃
    rw [← ψ.app_add (φ.isGenPt_app P₁ h₁) (φ.isGenPt_app P₂ h₂) h₃']
    congr 1⟩⟩

theorem comp_val (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).1 = Point.map φ.comap ψ.1 := by
  rw [comap_eq_genEval]; rfl

theorem app_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') {L : Type*} [Field L] [Algebra F L]
    [DecidableEq L] (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P) :
    (ψ.comp φ).app P hP = ψ.app (φ.app P hP) (φ.isGenPt_app P hP) := by
  show Point.map _ (ψ.app φ.1 φ.isGenPt) = _
  rw [map_app]
  rfl

theorem comap_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).comap = φ.comap.comp ψ.comap := by
  apply algHom_eq_of_map_genericPoint' E''
  rw [map_comap_genericPoint, ← Point.map_map, map_comap_genericPoint, comp_val]

theorem degree_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).degree = ψ.degree * φ.degree := by
  have h1 : (ψ.comp φ).comap.fieldRange = ψ.comap.fieldRange.map φ.comap := by
    rw [comap_comp, ← map_top_eq_fieldRange, ← map_top_eq_fieldRange, ← IntermediateField.map_map]
  have h2 : φ.comap.fieldRange = (⊤ : IntermediateField F E'.toAffine.FunctionField).map φ.comap :=
    (map_top_eq_fieldRange _).symm
  have hle : (ψ.comp φ).comap.fieldRange ≤ φ.comap.fieldRange := by
    rw [h1, h2]; exact IntermediateField.map_mono _ le_top
  have t := relfinrank_mul_relfinrank hle (le_top : φ.comap.fieldRange ≤ ⊤)
  have e : relfinrank (ψ.comp φ).comap.fieldRange φ.comap.fieldRange = ψ.degree := by
    rw [h1, h2, relfinrank_map_map, relfinrank_top_right]; rfl
  have hd : (ψ.comp φ).degree = relfinrank (ψ.comp φ).comap.fieldRange ⊤ := by
    rw [degree, relfinrank_top_right]
  rw [hd, ← t, e, relfinrank_top_right]
  rfl

end Isogeny

end App

section AlgClosed

variable [IsAlgClosed F] [DecidableEq F]

theorem exists_algebraMap_eq_of_isAlgebraic' {L : Type*} [Field L] [Algebra F L] {u : L}
    (hu : IsAlgebraic F u) : ∃ c : F, algebraMap F L c = u := by
  have hint := hu.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp (natDegree_eq_of_degree_eq_some hdeg)
  exact ⟨c, hc⟩

noncomputable def constMap (E : WeierstrassCurve F) (L : Type*) [Field L] [Algebra F L]
    [DecidableEq L] : E.toAffine.Point →+ (E.baseChange L).toAffine.Point :=
  Point.map (W' := E) (Algebra.ofId F L)

omit [IsAlgClosed F] in
theorem constMap_injective (E : WeierstrassCurve F) (L : Type*) [Field L] [Algebra F L]
    [DecidableEq L] : Function.Injective (constMap E L) :=
  Point.map_injective (W' := E) (Algebra.ofId F L)

omit [IsAlgClosed F] in
theorem map_constMap (E : WeierstrassCurve F) {L L' : Type*} [Field L] [Algebra F L] [Field L']
    [Algebra F L'] [DecidableEq L] [DecidableEq L'] (σ : L →ₐ[F] L') (c : E.toAffine.Point) :
    Point.map σ (constMap E L c) = constMap E L' c := by
  cases c with
  | zero => rfl
  | some x y h =>
    show Point.some _ _ _ = Point.some _ _ _
    simp only [Point.some.injEq]
    exact ⟨σ.commutes x, σ.commutes y⟩

theorem exists_map_eq_of_not_isGenPt (E : WeierstrassCurve F) {L : Type*} [Field L] [Algebra F L]
    [DecidableEq L] (P : (E.baseChange L).toAffine.Point) (hP : ¬ IsGenPt E P) :
    ∃ c : E.toAffine.Point, constMap E L c = P := by
  cases P with
  | zero => exact ⟨0, map_zero _⟩
  | some x y h =>
    have hx : IsAlgebraic F x := by
      by_contra hx; exact hP hx
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic' hx
    have heq := (equation_iff _ _).mp h.1
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq
    have hyalg : IsAlgebraic F y := by
      refine ⟨X ^ 2 + C (E.a₁ * c + E.a₃) * X - C (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆), ?_, ?_⟩
      · intro h0
        have := congrArg natDegree h0
        rw [natDegree_zero] at this
        have h2 : (X ^ 2 + C (E.a₁ * c + E.a₃) * X -
            C (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆) : F[X]).natDegree = 2 := by
          compute_degree!
        omega
      · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hc]
        linear_combination heq
    obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_isAlgebraic' hyalg
    have hcd : E.toAffine.Nonsingular c d := by
      have h' := h
      rw [← hc, ← hd] at h'
      exact (E.toAffine.baseChange_nonsingular (f := Algebra.ofId F L)
        (algebraMap F L).injective c d).mp h'
    refine ⟨.some c d hcd, ?_⟩
    show Point.some _ _ _ = Point.some _ _ _
    simp only [Point.some.injEq]
    exact ⟨hc, hd⟩

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem isGenPt_genericPoint : IsGenPt E (genericPoint E) := transcendental_genX E

theorem isGenPt_two_smul_genericPoint : IsGenPt E (genericPoint E + genericPoint E) := by
  rw [← two_zsmul]
  exact (mulIsogeny E 2 two_ne_zero).isGenPt

omit [IsAlgClosed F] [DecidableEq F] in
theorem isGenPt_neg {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {P : (E.baseChange L).toAffine.Point} (hP : IsGenPt E P) : IsGenPt E (-P) := by
  cases P with
  | zero => exact hP.elim
  | some x y h => exact hP

omit [IsAlgClosed F] [DecidableEq F] in
theorem isGenPt_add_self {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    {P : (E.baseChange L).toAffine.Point} (hP : IsGenPt E P) : IsGenPt E (P + P) := by
  rw [← map_genEval_genericPoint E P hP, ← map_add]
  exact isGenPt_map E _ (by rw [← two_zsmul]; exact (mulIsogeny E 2 two_ne_zero).isGenPt)

omit [IsAlgClosed F] [DecidableEq F] in

theorem map_genEval_neg {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point}
    (hQ : RespectsAdd E E' Q) {L : Type u} [Field L] [Algebra F L] [DecidableEq L]
    {P : (E.baseChange L).toAffine.Point} (hP : IsGenPt E P) :
    Point.map (genEval E (-P) (isGenPt_neg hP)) Q = -Point.map (genEval E P hP) Q := by
  have e₁ := (respectsAdd_iff Q).mp hQ L P P hP hP (isGenPt_add_self hP)
  have h2 : IsGenPt E (P + P + -P) := by rw [add_neg_cancel_right]; exact hP
  have e₂ := (respectsAdd_iff Q).mp hQ L (P + P) (-P) (isGenPt_add_self hP) (isGenPt_neg hP) h2
  rw [genEval_congr E (add_neg_cancel_right P P) h2 hP, e₁] at e₂
  rw [eq_neg_iff_add_eq_zero]
  have := congrArg (· - Point.map (genEval E P hP) Q) e₂
  rw [← sub_eq_zero.mpr this.symm]
  abel

theorem eq_zero_of_respectsAdd_map (c : E'.toAffine.Point)
    (h : RespectsAdd E E' (constMap E' E.toAffine.FunctionField c)) : c = 0 := by
  have e := (respectsAdd_iff _).mp h E.toAffine.FunctionField (genericPoint E) (genericPoint E)
    isGenPt_genericPoint isGenPt_genericPoint isGenPt_two_smul_genericPoint
  simp only [map_constMap, left_eq_add] at e
  exact constMap_injective E' _ (by rw [e, map_zero])

theorem mem_isogHom_iff {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} :
    Q ∈ isogHom E E' ↔ Q = 0 ∨ IsIsogeny E E' Q := by
  constructor
  · intro hQ
    by_cases hg : IsGenPt E' Q
    · exact Or.inr ((isIsogeny_iff Q).mpr ⟨hg, hQ⟩)
    · obtain ⟨c, rfl⟩ := exists_map_eq_of_not_isGenPt E' Q hg
      rw [eq_zero_of_respectsAdd_map c hQ, map_zero]
      exact Or.inl rfl
  · rintro (rfl | h)
    · exact zero_mem _
    · exact h.2

theorem isGenPt_of_mem_isogHom {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point}
    (hQ : Q ∈ isogHom E E') (h0 : Q ≠ 0) : IsGenPt E' Q :=
  ((isIsogeny_iff Q).mp ((mem_isogHom_iff.mp hQ).resolve_left h0)).1

omit [IsAlgClosed F] [DecidableEq F] in

theorem respectsAdd_map_genEval {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point}
    (hQ : RespectsAdd E E' Q) (hg : IsGenPt E' Q)
    {R : (E''.baseChange E'.toAffine.FunctionField).toAffine.Point} (hR : RespectsAdd E' E'' R) :
    RespectsAdd E E'' (Point.map (genEval E' Q hg) R) := by
  rw [respectsAdd_iff] at hQ hR ⊢
  intro L _ _ _ P₁ P₂ h₁ h₂ h₃
  have key : ∀ (P : (E.baseChange L).toAffine.Point) (hP : IsGenPt E P),
      Point.map (genEval E P hP) (Point.map (genEval E' Q hg) R) =
        Point.map (genEval E' (Point.map (genEval E P hP) Q) (isGenPt_map E' _ hg)) R := by
    intro P hP
    rw [Point.map_map, genEval_map]
  rw [key, key, key]
  have e := hQ L P₁ P₂ h₁ h₂ h₃
  have h₃' : IsGenPt E' (Point.map (genEval E P₁ h₁) Q + Point.map (genEval E P₂ h₂) Q) :=
    e ▸ isGenPt_map E' _ hg
  rw [genEval_congr E' e _ h₃']
  exact hR L _ _ _ _ h₃'

variable (E) in

abbrev isogEnd : Type u := isogHom E E

noncomputable def homComp (R : isogHom E' E'') (Q : isogHom E E') : isogHom E E'' :=
  open Classical in
  if h : IsGenPt E' Q.1 then ⟨Point.map (genEval E' Q.1 h) R.1,
    respectsAdd_map_genEval Q.2 h R.2⟩ else 0

theorem homComp_of_isGenPt (R : isogHom E' E'') (Q : isogHom E E') (h : IsGenPt E' Q.1) :
    (homComp R Q).1 = Point.map (genEval E' Q.1 h) R.1 := by
  rw [homComp, dif_pos h]

theorem homComp_of_not_isGenPt (R : isogHom E' E'') (Q : isogHom E E') (h : ¬ IsGenPt E' Q.1) :
    homComp R Q = 0 := by
  rw [homComp, dif_neg h]

theorem eq_zero_of_not_isGenPt (Q : isogHom E E') (h : ¬ IsGenPt E' Q.1) : Q = 0 := by
  rcases mem_isogHom_iff.mp Q.2 with h0 | h1
  · exact Subtype.ext h0
  · exact absurd ((isIsogeny_iff _).mp h1).1 h

theorem homComp_zero_right (R : isogHom E' E'') : homComp R (0 : isogHom E E') = 0 :=
  homComp_of_not_isGenPt _ _ (fun h => h)

theorem homComp_zero_left (Q : isogHom E E') : homComp (0 : isogHom E' E'') Q = 0 := by
  by_cases h : IsGenPt E' Q.1
  · exact Subtype.ext (by rw [homComp_of_isGenPt _ _ h]; exact map_zero _)
  · exact homComp_of_not_isGenPt _ _ h

theorem homComp_add_left (R₁ R₂ : isogHom E' E'') (Q : isogHom E E') :
    homComp (R₁ + R₂) Q = homComp R₁ Q + homComp R₂ Q := by
  by_cases h : IsGenPt E' Q.1
  · exact Subtype.ext (by
      simp only [AddSubgroup.coe_add, homComp_of_isGenPt _ _ h]; exact map_add _ _ _)
  · rw [homComp_of_not_isGenPt _ _ h, homComp_of_not_isGenPt _ _ h,
      homComp_of_not_isGenPt _ _ h, add_zero]

theorem homComp_add_right (R : isogHom E' E'') (Q₁ Q₂ : isogHom E E') :
    homComp R (Q₁ + Q₂) = homComp R Q₁ + homComp R Q₂ := by
  by_cases h₁ : IsGenPt E' Q₁.1
  · by_cases h₂ : IsGenPt E' Q₂.1
    · by_cases h₃ : IsGenPt E' (Q₁ + Q₂).1
      · refine Subtype.ext ?_
        simp only [AddSubgroup.coe_add, homComp_of_isGenPt _ _ h₁, homComp_of_isGenPt _ _ h₂,
          homComp_of_isGenPt _ _ h₃]
        exact (respectsAdd_iff R.1).mp R.2 E.toAffine.FunctionField Q₁.1 Q₂.1 h₁ h₂ h₃
      · have h0 : Q₁ + Q₂ = 0 := eq_zero_of_not_isGenPt _ h₃
        have hQ₂ : Q₂ = -Q₁ := eq_neg_of_add_eq_zero_right h0
        rw [h0, homComp_zero_right, eq_comm, add_eq_zero_iff_eq_neg]
        refine Subtype.ext ?_
        subst hQ₂
        simp only [AddSubgroup.coe_neg, homComp_of_isGenPt _ _ h₁]
        rw [homComp_of_isGenPt _ _ h₂]
        have := map_genEval_neg R.2 h₁
        rw [genEval_congr E' (AddSubgroup.coe_neg (isogHom E E') Q₁) h₂
          (isGenPt_neg h₁), this, neg_neg]
    · rw [eq_zero_of_not_isGenPt _ h₂, add_zero, homComp_zero_right, add_zero]
  · rw [eq_zero_of_not_isGenPt _ h₁, zero_add, homComp_zero_right, zero_add]

theorem homComp_assoc {E''' : WeierstrassCurve F} [E'''.IsElliptic] (S : isogHom E'' E''')
    (R : isogHom E' E'') (Q : isogHom E E') : homComp (homComp S R) Q = homComp S (homComp R Q) := by
  by_cases hQ : IsGenPt E' Q.1
  · by_cases hR : IsGenPt E'' R.1
    · have hRQ : IsGenPt E'' (homComp R Q).1 := by
        rw [homComp_of_isGenPt _ _ hQ]; exact isGenPt_map E'' _ hR
      refine Subtype.ext ?_
      rw [homComp_of_isGenPt _ _ hQ, homComp_of_isGenPt _ _ hR, homComp_of_isGenPt _ _ hRQ,
        Point.map_map]
      congr 1
      rw [genEval_congr E'' (homComp_of_isGenPt R Q hQ) hRQ (isGenPt_map E'' _ hR), genEval_map]
    · rw [eq_zero_of_not_isGenPt _ hR, homComp_zero_right, homComp_zero_left, homComp_zero_left,
        homComp_zero_right]
  · rw [eq_zero_of_not_isGenPt _ hQ, homComp_zero_right, homComp_zero_right, homComp_zero_right]

noncomputable def homId : isogEnd E := ⟨genericPoint E, respectsAdd_genericPoint⟩

theorem homComp_id_right (Q : isogHom E E') : homComp Q homId = Q := by
  refine Subtype.ext ?_
  rw [homComp_of_isGenPt _ _ isGenPt_genericPoint]
  show Point.map (genEval E (genericPoint E) isGenPt_genericPoint) Q.1 = Q.1
  rw [← eq_genEval E (AlgHom.id F _) (by cases genericPoint E <;> rfl) isGenPt_genericPoint]
  cases Q.1 <;> rfl

theorem homComp_id_left (Q : isogHom E E') : homComp homId Q = Q := by
  by_cases h : IsGenPt E' Q.1
  · exact Subtype.ext (by rw [homComp_of_isGenPt _ _ h]; exact map_genEval_genericPoint E' _ h)
  · rw [homComp_of_not_isGenPt _ _ h, eq_zero_of_not_isGenPt _ h]

noncomputable instance : Ring (isogEnd E) :=
  { (inferInstance : AddCommGroup (isogEnd E)) with
    mul := homComp
    one := homId
    mul_assoc := homComp_assoc
    one_mul := homComp_id_left
    mul_one := homComp_id_right
    left_distrib := homComp_add_right
    right_distrib := homComp_add_left
    zero_mul := homComp_zero_left
    mul_zero := homComp_zero_right }

theorem isogEnd_mul_def (a b : isogEnd E) : a * b = homComp a b := rfl

instance : IsDomain (isogEnd E) := by
  have : NoZeroDivisors (isogEnd E) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push_neg at hne
    have hb : IsGenPt E b.1 := isGenPt_of_mem_isogHom b.2 (fun h => hne.2 (Subtype.ext h))
    have ha : IsGenPt E a.1 := isGenPt_of_mem_isogHom a.2 (fun h => hne.1 (Subtype.ext h))
    have := congrArg Subtype.val hab
    rw [isogEnd_mul_def, homComp_of_isGenPt _ _ hb] at this
    exact isGenPt_ne_zero E (isGenPt_map E _ ha) this
  have : Nontrivial (isogEnd E) := ⟨⟨1, 0, fun h =>
    isGenPt_ne_zero E (isGenPt_genericPoint (E := E)) (congrArg Subtype.val h)⟩⟩
  exact NoZeroDivisors.to_isDomain _

end AlgClosed

end GroundTheory.Arith.Abelian
