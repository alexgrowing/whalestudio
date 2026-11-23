import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S

theorem locE_isUnit_or_exists_algEquiv_prod_swap {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) :
    (∀ x : E, x ≠ 0 → IsUnit x) ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap := by
  classical
  have hrank := L.rank
  have : Module.Free F E := L.free
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [hrank]; norm_num)
  have : IsReduced E := L.reduced
  by_cases hfield : ∀ x : E, x ≠ 0 → IsUnit x
  · exact Or.inl hfield
  right
  obtain ⟨x, hx⟩ := not_forall.1 hfield
  obtain ⟨hx0, hxu⟩ := _root_.not_imp.1 hx
  have hfix : ∀ y : E, L.cj y = y → ∃ a : F, algebraMap F E a = y := fun y hy => (L.cj_fix y).1 hy
  obtain ⟨a, ha⟩ := hfix (x * L.cj x) (by rw [map_mul, L.cj_cj, mul_comm])
  have hN : x * L.cj x = 0 := by
    by_contra hne
    apply hxu
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact hne ha.symm
    refine IsUnit.of_mul_eq_one (L.cj x * algebraMap F E a⁻¹) ?_
    rw [← mul_assoc, ← ha, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  obtain ⟨t, ht⟩ := hfix (x + L.cj x) (by rw [map_add, L.cj_cj, add_comm])
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    have hc : L.cj x = -x := by linear_combination -ht
    have hsq : x ^ 2 = 0 := by
      rw [hc] at hN
      linear_combination -hN
    exact hx0 (IsReduced.eq_zero x ⟨2, hsq⟩)
  have hcu : L.cj (algebraMap F E t⁻¹) = algebraMap F E t⁻¹ := L.cj.commutes _
  have hpq : x * algebraMap F E t⁻¹ + L.cj x * algebraMap F E t⁻¹ = 1 := by
    rw [← add_mul, ← ht, ← map_mul, mul_inv_cancel₀ ht0, map_one]
  set p := x * algebraMap F E t⁻¹ with hp
  set q := L.cj x * algebraMap F E t⁻¹ with hq
  have hpq0 : p * q = 0 := by
    rw [hp, hq]
    linear_combination (algebraMap F E t⁻¹ * algebraMap F E t⁻¹) * hN
  have hqp : q * p = 0 := by rw [mul_comm]; exact hpq0
  have hcp : L.cj p = q := by rw [hp, hq, map_mul, hcu]
  have hcq : L.cj q = p := by rw [hp, hq, map_mul, hcu, L.cj_cj]
  have hpp : p * p = p := by
    have h : p * (p + q) = p := by rw [hpq, mul_one]
    linear_combination h - hpq0
  have hqq : q * q = q := by
    have h : (p + q) * q = q := by rw [hpq, one_mul]
    linear_combination h - hpq0
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : q = 1 := by rw [← hpq, h, zero_add]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcp, h, map_zero]
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : p = 1 := by rw [← hpq, h, add_zero]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcq, h, map_zero]
  let g : (F × F) →ₐ[F] E :=
    { toFun := fun z => z.1 • p + z.2 • q
      map_one' := by simp [hpq]
      map_mul' := fun z w => by
        simp only [Prod.fst_mul, Prod.snd_mul, Algebra.smul_def, map_mul]
        linear_combination (-(algebraMap F E z.1 * algebraMap F E w.1)) * hpp -
          (algebraMap F E z.2 * algebraMap F E w.2) * hqq -
          (algebraMap F E z.1 * algebraMap F E w.2 + algebraMap F E z.2 * algebraMap F E w.1) * hpq0
      map_zero' := by simp
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      commutes' := fun r => by
        simp only [Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [← smul_add, hpq, Algebra.algebraMap_eq_smul_one] }
  have ginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : z.1 • p + z.2 • q = 0 := hz
    have h1 : z.1 • p = 0 := by
      have h := congrArg (· * p) hz'
      simp only [add_mul, smul_mul_assoc, hpp, hqp, smul_zero, add_zero, zero_mul] at h
      exact h
    have h2 : z.2 • q = 0 := by
      have h := congrArg (· * q) hz'
      simp only [add_mul, smul_mul_assoc, hqq, hpq0, smul_zero, zero_add, zero_mul] at h
      exact h
    rw [smul_eq_zero] at h1 h2
    exact Prod.ext (h1.resolve_right hp0) (h2.resolve_right hq0)
  have gsurj : Function.Surjective g := by
    have hdim : Module.finrank F (F × F) = Module.finrank F E := by
      rw [Module.finrank_prod, Module.finrank_self, hrank]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := g.toLinearMap)).1 ginj
  let e0 := AlgEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := gsurj y
  have hez : e0.symm (g z) = z := e0.symm_apply_apply z
  have hcz : L.cj (g z) = g z.swap := by
    show L.cj (z.1 • p + z.2 • q) = z.2 • p + z.1 • q
    rw [map_add, map_smul, map_smul, hcp, hcq, add_comm]
  rw [hcz, hez]
  exact e0.symm_apply_apply z.swap

end PI.UnitaryGroupMassFormula.CntFormula
