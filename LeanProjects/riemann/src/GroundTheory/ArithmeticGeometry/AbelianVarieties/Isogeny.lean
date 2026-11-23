import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FunctionFieldPoint

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F]

section Defs

def yOf {K : Type*} [Field K] (W : WeierstrassCurve K) : W.toAffine.Point → K
  | .zero => 0
  | .some _ y _ => y

theorem eq_some_xOf_yOf {K : Type*} [Field K] (W : WeierstrassCurve K) {P : W.toAffine.Point}
    (hP : P ≠ 0) : ∃ h : W.toAffine.Nonsingular (xOf W P) (yOf W P), P = .some _ _ h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨h, rfl⟩

variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]

noncomputable def ratMapValue (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)
    {L : Type u} [Field L] [Algebra F L] [DecidableEq L] {u v : L}
    (h : (E.baseChange L).toAffine.Equation u v)
    (hu : Transcendental F u) : (E'.baseChange L).toAffine.Point :=
  Point.map (liftPoint E h hu) Q

def RespectsAdd (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra F L] [DecidableEq L] (u₁ v₁ u₂ v₂ u₃ v₃ : L)
    (h₁ : (E.baseChange L).toAffine.Nonsingular u₁ v₁)
    (h₂ : (E.baseChange L).toAffine.Nonsingular u₂ v₂)
    (h₃ : (E.baseChange L).toAffine.Nonsingular u₃ v₃)
    (t₁ : Transcendental F u₁) (t₂ : Transcendental F u₂) (t₃ : Transcendental F u₃),
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ = Point.some u₃ v₃ h₃ →
      ratMapValue E E' Q h₃.1 t₃ = ratMapValue E E' Q h₁.1 t₁ + ratMapValue E E' Q h₂.1 t₂

def IsIsogeny (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) : Prop :=
  (∃ (x y : E.toAffine.FunctionField)
    (h : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular x y),
      Q = .some x y h ∧ Transcendental F x) ∧ RespectsAdd E E' Q

def Isogeny : Type u :=
  {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point // IsIsogeny E E' Q}

namespace Isogeny

variable {E E'} (φ : Isogeny E E')

noncomputable def x : E.toAffine.FunctionField := xOf _ φ.1

noncomputable def y : E.toAffine.FunctionField := yOf _ φ.1

omit [E.IsElliptic] [E'.IsElliptic] in
theorem nonsingular : (E'.baseChange E.toAffine.FunctionField).toAffine.Nonsingular φ.x φ.y := by
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  simp only [Isogeny.x, Isogeny.y, he]
  exact h

omit [E.IsElliptic] [E'.IsElliptic] in
theorem transcendental_alt : Transcendental F φ.x := by
  obtain ⟨⟨x, y, h, he, ht⟩, -⟩ := φ.2
  simp only [Isogeny.x, he]
  exact ht

noncomputable def comap : E'.toAffine.FunctionField →ₐ[F] E.toAffine.FunctionField :=
  liftPoint E' φ.nonsingular.1 φ.transcendental_alt

omit [E.IsElliptic] [E'.IsElliptic] in
theorem comap_genX : φ.comap (genX E') = φ.x := liftPoint_genX _ _ _

omit [E.IsElliptic] [E'.IsElliptic] in
theorem comap_genY : φ.comap (genY E') = φ.y := liftPoint_genY _ _ _

noncomputable def degree : ℕ :=
  Module.finrank φ.comap.fieldRange E.toAffine.FunctionField

def IsSeparable : Prop :=
  Algebra.IsSeparable φ.comap.fieldRange E.toAffine.FunctionField

end Isogeny

end Defs

section Mul

variable (E : WeierstrassCurve F) [E.IsElliptic]

noncomputable def ratEmb : RatFunc F →ₐ[F] E.toAffine.FunctionField :=
  RatFunc.liftAlgHom (aeval (genX E)) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.mp (transcendental_genX E)))

omit [E.IsElliptic] in
theorem ratEmb_injective : Function.Injective (ratEmb E) :=
  RatFunc.liftAlgHom_injective _ (transcendental_iff_injective.mp (transcendental_genX E))

omit [E.IsElliptic] in
theorem ratEmb_div (p q : F[X]) :
    ratEmb E (algebraMap _ _ p / algebraMap _ _ q) = aeval (genX E) p / aeval (genX E) q :=
  RatFunc.liftAlgHom_apply_div _ _ p q

omit [E.IsElliptic] in
theorem ratEmb_X : ratEmb E RatFunc.X = genX E := by
  have := ratEmb_div E X 1
  rw [map_one, div_one, map_one, div_one, aeval_X, RatFunc.algebraMap_X] at this
  exact this

theorem map_top_eq_fieldRange {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L]
    (f : K →ₐ[F] L) : (⊤ : IntermediateField F K).map f = f.fieldRange := by
  ext z
  simp only [IntermediateField.mem_map, IntermediateField.mem_top, true_and, AlgHom.mem_fieldRange]

omit [E.IsElliptic] in
theorem fieldRange_ratEmb : (ratEmb E).fieldRange = F⟮genX E⟯ := by
  rw [← map_top_eq_fieldRange, ← RatFunc.adjoin_X, adjoin_map, Set.image_singleton, ratEmb_X]

theorem aeval_genX_ΨSq_ne_zero {n : ℤ} (hn : n ≠ 0) : aeval (genX E) (E.ΨSq n) ≠ 0 := by
  rw [ne_eq, aeval_genX_eq_zero_iff]
  exact ΨSq_ne_zero_of_ne_zero E hn

omit [E.IsElliptic] in
private theorem baseChange_eval (p : F[X]) :
    (p.map (algebraMap F E.toAffine.FunctionField)).eval (genX E) = aeval (genX E) p :=
  eval_map_algebraMap _ _

theorem genericPoint_eq :
    genericPoint E = .some (genX E) (genY E) (equation_iff_nonsingular.mp (equation_gen E)) :=
  rfl

theorem zsmul_genericPoint_ne_zero {n : ℤ} (hn : n ≠ 0) : n • genericPoint E ≠ 0 := by
  rw [genericPoint_eq, ne_eq, zsmul_eq_zero_iff]
  show ¬((E.map (algebraMap F E.toAffine.FunctionField)).ΨSq n).eval (genX E) = 0
  rw [map_ΨSq, baseChange_eval]
  exact aeval_genX_ΨSq_ne_zero E hn

theorem xOf_zsmul_genericPoint {n : ℤ} (hn : n ≠ 0) :
    xOf _ (n • genericPoint E) = aeval (genX E) (E.Φ n) / aeval (genX E) (E.ΨSq n) := by
  rw [genericPoint_eq, xOf_zsmul]
  · show ((E.map (algebraMap F E.toAffine.FunctionField)).Φ n).eval (genX E) /
      ((E.map (algebraMap F E.toAffine.FunctionField)).ΨSq n).eval (genX E) = _
    rw [map_Φ, map_ΨSq, baseChange_eval, baseChange_eval]
  · show ((E.map (algebraMap F E.toAffine.FunctionField)).ΨSq n).eval (genX E) ≠ 0
    rw [map_ΨSq, baseChange_eval]
    exact aeval_genX_ΨSq_ne_zero E hn

noncomputable def ratΦΨ (n : ℤ) : RatFunc F :=
  algebraMap _ _ (E.Φ n) / algebraMap _ _ (E.ΨSq n)

omit [E.IsElliptic] in
theorem ratEmb_ratΦΨ (n : ℤ) :
    ratEmb E (ratΦΨ E n) = aeval (genX E) (E.Φ n) / aeval (genX E) (E.ΨSq n) :=
  ratEmb_div E _ _

theorem max_natDegree_ratΦΨ {n : ℤ} (hn : n ≠ 0) :
    max (ratΦΨ E n).num.natDegree (ratΦΨ E n).denom.natDegree = n.natAbs ^ 2 := by
  have hΨ0 : E.ΨSq n ≠ 0 := ΨSq_ne_zero_of_ne_zero E hn
  have hN : 0 < n.natAbs ^ 2 := by have := Int.natAbs_pos.mpr hn; positivity
  have hΦdeg := natDegree_Φ E n
  have hΦ0 : E.Φ n ≠ 0 := fun h => by rw [h, natDegree_zero] at hΦdeg; omega
  have hnum_dvd : (ratΦΨ E n).num ∣ E.Φ n := RatFunc.num_div_dvd _ hΨ0
  have hden_dvd : (ratΦΨ E n).denom ∣ E.ΨSq n := RatFunc.denom_div_dvd _ _
  have hrf0 : ratΦΨ E n ≠ 0 := div_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hΦ0)
    ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hΨ0)
  have hnum0 : (ratΦΨ E n).num ≠ 0 := by rwa [ne_eq, RatFunc.num_eq_zero_iff]
  have hcross : (ratΦΨ E n).num * E.ΨSq n = E.Φ n * (ratΦΨ E n).denom := by
    have h1 := RatFunc.num_div_denom (ratΦΨ E n)
    conv_rhs at h1 => rw [ratΦΨ]
    have hb : algebraMap F[X] (RatFunc F) (ratΦΨ E n).denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _)
    have hd : algebraMap F[X] (RatFunc F) (E.ΨSq n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hΨ0
    rw [div_eq_div_iff hb hd, ← map_mul, ← map_mul] at h1
    exact IsFractionRing.injective F[X] (RatFunc F) h1
  have hΦ_dvd : E.Φ n ∣ (ratΦΨ E n).num :=
    (isCoprime_Φ_ΨSq E n).dvd_of_dvd_mul_right ⟨_, hcross⟩
  have hnum : (ratΦΨ E n).num.natDegree = n.natAbs ^ 2 :=
    le_antisymm (hΦdeg ▸ natDegree_le_of_dvd hnum_dvd hΦ0)
      (hΦdeg ▸ natDegree_le_of_dvd hΦ_dvd hnum0)
  have hden : (ratΦΨ E n).denom.natDegree ≤ n.natAbs ^ 2 - 1 :=
    (natDegree_le_of_dvd hden_dvd hΨ0).trans (natDegree_ΨSq_le E n)
  rw [hnum]
  exact max_eq_left (hden.trans (Nat.sub_le _ _))

theorem transcendental_ratΦΨ {n : ℤ} (hn : n ≠ 0) : Transcendental F (ratΦΨ E n) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  have h := max_natDegree_ratΦΨ E hn
  rw [hc, RatFunc.num_C, RatFunc.denom_C, natDegree_C, natDegree_one, max_self] at h
  have := Int.natAbs_pos.mpr hn
  have : 0 < n.natAbs ^ 2 := by positivity
  omega

noncomputable def mulIsogeny (n : ℤ) (hn : n ≠ 0) : Isogeny E E :=
  ⟨n • genericPoint E, by
    obtain ⟨h, he⟩ := eq_some_xOf_yOf _ (zsmul_genericPoint_ne_zero E hn)
    refine ⟨⟨_, _, h, he, ?_⟩, ?_⟩
    · rw [xOf_zsmul_genericPoint E hn, ← ratEmb_ratΦΨ]
      intro halg
      exact transcendental_ratΦΨ E hn ((isAlgebraic_algHom_iff _ (ratEmb_injective E)).mp halg)
    · intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ h₁ h₂ h₃ t₁ t₂ t₃ hadd
      simp only [ratMapValue, map_zsmul]
      rw [map_liftPoint_genericPoint E h₁ t₁, map_liftPoint_genericPoint E h₂ t₂,
        map_liftPoint_genericPoint E h₃ t₃, ← hadd, zsmul_add]⟩

theorem mulIsogeny_alt {n : ℤ} (hn : n ≠ 0) :
    (mulIsogeny E n hn).x = aeval (genX E) (E.Φ n) / aeval (genX E) (E.ΨSq n) :=
  xOf_zsmul_genericPoint E hn

end Mul

section Degree

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem finrank_adjoin_ratΦΨ {n : ℤ} (hn : n ≠ 0) :
    Module.finrank (IntermediateField.adjoin F {ratΦΨ E n}) (RatFunc F) = n.natAbs ^ 2 := by
  rw [RatFunc.finrank_eq_max_natDegree, max_natDegree_ratΦΨ E hn]

theorem degree_mulIsogeny {n : ℤ} (hn : n ≠ 0) : (mulIsogeny E n hn).degree = n.natAbs ^ 2 := by
  set φ := mulIsogeny E n hn
  set α := φ.comap
  set E1 : IntermediateField F E.toAffine.FunctionField := F⟮genX E⟯
  set M := α.fieldRange
  set E0 : IntermediateField F E.toAffine.FunctionField := F⟮φ.x⟯
  have hx : φ.x = ratEmb E (ratΦΨ E n) := by rw [ratEmb_ratΦΨ]; exact mulIsogeny_alt E hn
  have hxE1 : φ.x ∈ E1 := by
    have hE1 : E1 = (ratEmb E).fieldRange := (fieldRange_ratEmb E).symm
    rw [hx, hE1]; exact ⟨_, rfl⟩
  have hxM : φ.x ∈ M := ⟨genX E, φ.comap_genX⟩
  have h01 : E0 ≤ E1 := adjoin_simple_le_iff.mpr hxE1
  have h0M : E0 ≤ M := adjoin_simple_le_iff.mpr hxM

  have e1 : relfinrank E1 ⊤ = 2 := by rw [relfinrank_top_right, finrank_adjoin_genX]

  have e2 : relfinrank E0 M = 2 := by
    have hE0 : E0 = E1.map α := by
      rw [adjoin_map, Set.image_singleton, φ.comap_genX]
    have hM : M = (⊤ : IntermediateField F _).map α := (map_top_eq_fieldRange α).symm
    rw [hE0, hM, relfinrank_map_map, e1]

  have e3 : relfinrank E0 E1 = n.natAbs ^ 2 := by
    have hE0 : E0 = (F⟮ratΦΨ E n⟯).map (ratEmb E) := by
      rw [adjoin_map, Set.image_singleton, ← hx]
    have hE1 : E1 = (⊤ : IntermediateField F (RatFunc F)).map (ratEmb E) := by
      rw [map_top_eq_fieldRange, fieldRange_ratEmb]
    rw [hE0, hE1, relfinrank_map_map, relfinrank_top_right, finrank_adjoin_ratΦΨ E hn]
  have t1 := relfinrank_mul_relfinrank h01 (le_top : E1 ≤ ⊤)
  have t2 := relfinrank_mul_relfinrank h0M (le_top : M ≤ ⊤)
  rw [e1, e3] at t1
  rw [e2, ← t1] at t2
  have hdeg : φ.degree = relfinrank M ⊤ := by rw [Isogeny.degree, relfinrank_top_right]
  rw [hdeg]
  omega

end Degree

section Separable

theorem isSeparable_of_quadratic {L K : Type*} [Field L] [Field K] [Algebra L K] {y : K} (b c : L)
    (hy : y ^ 2 + algebraMap L K b * y - algebraMap L K c = 0)
    (hD' : algebraMap L K b ^ 2 + 4 * algebraMap L K c ≠ 0) :
    IsSeparable L y := by
  have hD : b ^ 2 + 4 * c ≠ 0 := fun h => hD' (by
    rw [← map_pow, ← map_ofNat (algebraMap L K) 4, ← map_mul, ← map_add, h, map_zero])
  have hq' : derivative (X ^ 2 + C b * X - C c : L[X]) = C 2 * X + C b := by
    simp only [derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul_X, derivative_C]
    simp
  have hsep : (X ^ 2 + C b * X - C c : L[X]).Separable := by
    rw [Polynomial.separable_def, hq']
    refine ⟨C (-4 * (b ^ 2 + 4 * c)⁻¹), C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b), ?_⟩
    have e : (C 2 * X + C b) ^ 2 - 4 * (X ^ 2 + C b * X - C c) = C (b ^ 2 + 4 * c) := by
      simp only [map_add, map_pow, map_mul, map_ofNat]; ring
    calc C (-4 * (b ^ 2 + 4 * c)⁻¹) * (X ^ 2 + C b * X - C c) +
          C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b) * (C 2 * X + C b)
        = C (b ^ 2 + 4 * c)⁻¹ * ((C 2 * X + C b) ^ 2 - 4 * (X ^ 2 + C b * X - C c)) := by
          simp only [map_mul, map_neg, map_ofNat]; ring
      _ = 1 := by rw [e, ← C_mul, inv_mul_cancel₀ hD, C_1]
  have hq : aeval y (X ^ 2 + C b * X - C c : L[X]) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
    exact hy
  exact hsep.of_dvd (minpoly.dvd L y hq)

variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem isSeparable_genY (L : IntermediateField F E.toAffine.FunctionField)
    (hL : L ≤ F⟮genX E⟯) : IsSeparable (extendScalars hL) (genY E) := by
  have hg : genX E ∈ extendScalars hL := (mem_extendScalars hL).mpr (mem_adjoin_simple_self F _)
  have hcst : ∀ a : F, algebraMap F E.toAffine.FunctionField a ∈ extendScalars hL := fun a =>
    (mem_extendScalars hL).mpr (IntermediateField.algebraMap_mem _ a)
  refine isSeparable_of_quadratic
    (⟨algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃, add_mem (mul_mem (hcst _) hg) (hcst _)⟩)
    (⟨genX E ^ 3 + algebraMap F _ E.a₂ * genX E ^ 2 + algebraMap F _ E.a₄ * genX E +
      algebraMap F _ E.a₆, add_mem (add_mem (add_mem (pow_mem hg 3)
        (mul_mem (hcst _) (pow_mem hg 2))) (mul_mem (hcst _) hg)) (hcst _)⟩) ?_ ?_
  · have e := (equation_iff _ _).mp (equation_gen E)
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
    change genY E ^ 2 + (algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃) * genY E -
      (genX E ^ 3 + algebraMap F _ E.a₂ * genX E ^ 2 + algebraMap F _ E.a₄ * genX E +
        algebraMap F _ E.a₆) = 0
    linear_combination e
  · intro h'
    simp only [IntermediateField.algebraMap_apply] at h'
    have : aeval (genX E) E.Ψ₂Sq = 0 := by
      rw [← h']
      simp only [Ψ₂Sq, map_add, map_mul, map_pow, aeval_C, aeval_X, b₂, b₄, b₆, map_ofNat]
      ring
    rw [aeval_genX_eq_zero_iff] at this
    exact Ψ₂Sq_ne_zero E this

end Separable

end GroundTheory.Arith.Abelian
