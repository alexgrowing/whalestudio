import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageFiniteProjective

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Pointwise

namespace GlobalTheory.ChainPts.SysB.RingJ

open GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.RingChain GlobalTheory.Sandwich

theorem dvd_iff_of_completion {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {q : A}
    (ec : AdicCompletion (Ideal.span {q}) A ≃+* R) (he : ∀ a, ec (algebraMap A _ a) = algebraMap A R a) {a : A}
    (ha : a ∣ q) (x : A) : algebraMap A R a ∣ algebraMap A R x ↔ a ∣ x := by
  refine ⟨fun ⟨r, hr⟩ => ?_, map_dvd _⟩
  obtain ⟨t, ht⟩ := ha
  obtain ⟨x', y, hy⟩ := LatDescent.adic_surj A q (ec.symm r)
  obtain ⟨b, hb⟩ := LatDescent.adic_inj A q (x - a * x') (algebraMap A _ a * y) (ec.injective (by
    have h1 := congrArg ec hy
    rw [ec.apply_symm_apply, map_add, map_mul, he, he] at h1
    rw [map_mul, map_mul, he, he, he, map_sub, map_mul, hr, h1]; ring))
  exact ⟨x' + t * b, by rw [mul_add, ← mul_assoc, ← ht, ← hb]; ring⟩

theorem ringJSt : RingJSt := by
  intro p _ D A _ GG pol ε c n o e π γ Lie Om _ _ _ _ cω pr C η hC _ hη hπ y x
  by_cases hp : IsUnit (p : A)
  · have hu : IsUnit π := isUnit_of_dvd_unit hπ hp
    refine ⟨fun _ j => hu.dvd, fun _ => ?_⟩
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (C.j y)
    rw [← hz, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists]
    obtain ⟨u, rfl⟩ := hu
    exact ⟨(↑u⁻¹ : A) • _, trivial, by rw [smul_smul, Units.mul_inv, one_smul]⟩
  obtain ⟨S, _, ec, he, hε, eL, eO, hL, -, hOf⟩ := hC hp
  subst e
  have key : ∀ j : Fin GG.height, algebraMap A S.R π ∣
      (c.baseChange S.R hε).alDual (eL (1 ⊗ₜ y)) j - algebraMap A S.R (pr y (η j)) := fun j => by
    obtain ⟨v, hv⟩ := (GG.omega_val_eq_zero_iff 1 (dlog GG (c.t' j) - cω (η j))).1 (by
      change (dlog GG (c.t' j)).1 1 - (cω (η j)).1 1 = 0
      rw [hη j]; exact sub_self _)
    have h1 : (c.baseChange S.R hε).alDual (eL (1 ⊗ₜ y)) j = eL (1 ⊗ₜ y) ((GG.toBase S.R).omega (dlog GG (c.t' j))) := by
      rw [← dlog_bcChar]; rfl
    rw [h1, ← hL, ← map_sub, ← map_sub, hv, map_smulₛₗ, map_smul, pow_one, smul_eq_mul]
    exact (map_dvd _ hπ).mul_right _
  rw [hOf.j y x, mem_base, ← hOf.pi_eq]
  have h2 : ∀ j : Fin GG.height, (π ∣ x.1 j - pr y (η j)) ↔ algebraMap A S.R π ∣
      algebraMap A S.R (x.1 j) - (c.baseChange S.R hε).alDual (eL (1 ⊗ₜ y)) j := fun j => by
    rw [← dvd_iff_of_completion ec he hπ, map_sub, ← sub_add_sub_cancel _ ((c.baseChange S.R hε).alDual (eL (1 ⊗ₜ y)) j)]
    exact dvd_add_left (key j)
  simp only [h2]
  refine ⟨fun ⟨z, hz⟩ j => ⟨z j, (congrFun hz j).symm⟩, fun h => ?_⟩
  choose z hz using h
  exact ⟨z, funext fun j => (hz j).symm⟩

end GlobalTheory.ChainPts.SysB.RingJ

end
