import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RowRawRange
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc

noncomputable def idemPairHom {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) : F × F →ₐ[F] E :=
  AlgHom.ofLinearMap
    ((LinearMap.toSpanSingleton F E p).coprod (LinearMap.toSpanSingleton F E q))
    (by simpa using h1)
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp only [Prod.mk_mul_mk, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, map_mul]
      linear_combination
        (-(algebraMap F E a * algebraMap F E c * p) - algebraMap F E b * algebraMap F E d * q) * h1
        + (algebraMap F E a * algebraMap F E c + algebraMap F E b * algebraMap F E d
          - algebraMap F E a * algebraMap F E d - algebraMap F E b * algebraMap F E c) * h0)

theorem idemPairHom_apply {F E : Type} [Field F] [CommRing E] [Algebra F E] (p q : E)
    (h1 : p + q = 1) (h0 : p * q = 0) (y : F × F) :
    idemPairHom p q h1 h0 y = y.1 • p + y.2 • q := rfl

theorem LocE_isField_or_split {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) :
    IsField E ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap := by
  by_cases hE : IsField E
  · exact Or.inl hE
  right
  haveI := L.reduced
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨x, hx0, hxu⟩ : ∃ x : E, x ≠ 0 ∧ ¬ IsUnit x := by
    by_contra hcon
    push Not at hcon
    exact hE ⟨exists_pair_ne E, mul_comm, fun {a} ha => (hcon a ha).exists_right_inv⟩
  obtain ⟨n, hn⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])
  have hn0 : n = 0 := by
    by_contra h
    apply hxu
    have : IsUnit (x * L.cj x) := hn ▸ (IsUnit.mk0 n h).map (algebraMap F E)
    exact isUnit_of_mul_isUnit_left this
  have hN : x * L.cj x = 0 := by rw [← hn, hn0, map_zero]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    apply hx0
    apply IsNilpotent.eq_zero
    exact ⟨2, by linear_combination (-x) * ht - hN⟩
  set p : E := t⁻¹ • x with hp
  have hq : L.cj p = t⁻¹ • L.cj x := by rw [hp, map_smul]
  have h1 : p + L.cj p = 1 := by
    rw [hq, hp, ← smul_add, ← ht, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ ht0, map_one]
  have h0 : p * L.cj p = 0 := by
    rw [hq, hp, smul_mul_smul_comm, hN, smul_zero]
  have hp0 : p ≠ 0 := smul_ne_zero (inv_ne_zero ht0) hx0
  have hq0 : L.cj p ≠ 0 := by simpa using hp0
  have hpp : p * p = p := by linear_combination p * h1 - h0
  have hqq : L.cj p * L.cj p = L.cj p := by linear_combination L.cj p * h1 - h0
  clear_value p
  let φ : F × F →ₐ[F] E := idemPairHom p (L.cj p) h1 h0
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    change a • p + b • L.cj p = 0 at hab
    have ha : a • p = 0 := by
      have := congrArg (p * ·) hab
      simpa [mul_add, hpp, h0] using this
    have hb : b • L.cj p = 0 := by rwa [ha, zero_add] at hab
    have ha' : a = 0 := (smul_eq_zero.1 ha).resolve_right hp0
    have hb' : b = 0 := (smul_eq_zero.1 hb).resolve_right hq0
    simp [ha', hb']
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (by rw [L.rank]; simp)).1 hinj
  refine ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := (AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).surjective z
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_eq]
  change L.cj (y.1 • p + y.2 • L.cj p) = y.2 • p + y.1 • L.cj p
  rw [map_add, map_smul, map_smul, L.cj_cj, add_comm]

theorem isIntegral_valInteger_iff {F : Type} [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] :=
  ⟨fun h => (Valuation.integer.integers (valuation F)).mem_of_integral h,
    fun h => isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := ⟨a, h⟩)⟩

theorem isField_or_split : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → IsField E ∨ ∃ e : E ≃ₐ[F] F × F, (∀ x, e (M.L.cj x) = (e x).swap) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x, x ∈ M.L.O ↔ ((e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) := by
  intro F _ _ _ E _ _ _ _ M hM
  rcases LocE_isField_or_split M.L with h | ⟨e, he⟩
  · exact Or.inl h
  haveI := hM.loc
  haveI := M.L.top
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  refine Or.inr ⟨e, he, ?_, ?_, fun x => ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  · exact IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  · rw [M.L.O_def, ← isIntegral_algEquiv (e.restrictScalars 𝒪[F]), ← isIntegral_valInteger_iff,
      ← isIntegral_valInteger_iff, ← IsIntegral.pair_iff]
    rfl

end GlobalTheory.SgLoc
