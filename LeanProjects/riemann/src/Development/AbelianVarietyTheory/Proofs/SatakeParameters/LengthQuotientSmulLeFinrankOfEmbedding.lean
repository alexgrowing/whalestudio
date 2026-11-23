import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMulStatement
open Pointwise

namespace GlobalTheory

theorem length_quotient_smul_range_le_finrank_mul : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] (W M : Type) [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] [FiniteDimensional K W] [AddCommGroup M] [Module O M] (f : M →ₗ[O] W), Function.Injective f → ∀ a : O, Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) ≤ (Module.finrank K W : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O K _ _ _ _ _ _ W M _ _ _ _ _ _ _ f hf a
  set R := LinearMap.range (a • (LinearMap.id : M →ₗ[O] M)) with hR
  refine GlobalTheory.T.length_le_of_forall_fg_submodule_length_le O (M ⧸ R) _ ?_
  intro N hN
  obtain ⟨s, hs⟩ := hN
  set g := Function.surjInv (Submodule.mkQ_surjective R) with hg
  have hgs : ∀ q, R.mkQ (g q) = q := Function.surjInv_eq (Submodule.mkQ_surjective R)
  let N' : Submodule O M := Submodule.span O (g '' (s : Set (M ⧸ R)))
  have hmap : N'.map R.mkQ = N := by
    rw [Submodule.map_span, ← hs, ← Set.image_comp]
    congr 1
    ext q
    simp [hgs]
  haveI : Module.Finite O N' := Module.Finite.iff_fg.mpr (Submodule.fg_span (s.finite_toSet.image g))
  let e : N' →ₗ[O] W := f ∘ₗ N'.subtype
  have he : Function.Injective e := hf.comp N'.injective_subtype
  haveI : Module.IsTorsionFree K W := inferInstance
  haveI : Module.IsTorsionFree O W :=
    Module.IsTorsionFree.comap (S := K) (algebraMap O K)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have hinj := IsFractionRing.injective O K
        have : r = 0 := hinj (by simpa using h0)
        subst this
        exact (not_isRegular_zero (R := O)) hr))
      (fun r m => algebraMap_smul K r m)
  haveI : Module.IsTorsionFree O N' := Function.Injective.moduleIsTorsionFree e he e.map_smul
  haveI : Module.Free O N' := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank O N' ≤ Module.finrank K W := by
    let b := Module.finBasis O N'
    have h1 : LinearIndependent O (e ∘ b) := b.linearIndependent.map' e (LinearMap.ker_eq_bot.mpr he)
    have h2 : LinearIndependent K (e ∘ b) := (LinearIndependent.iff_fractionRing O K).mp h1
    simpa using h2.fintype_card_le_finrank
  let p : N' →ₗ[O] N := (R.mkQ ∘ₗ N'.subtype).codRestrict N (by
    intro x
    rw [← hmap]
    exact ⟨x, x.2, rfl⟩)
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let R' := LinearMap.range (a • (LinearMap.id : N' →ₗ[O] N'))
  have hker : R' ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    have : R.mkQ (a • (x : M)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, by simp⟩
    simpa [p] using this
  let q : (N' ⧸ R') →ₗ[O] N := R'.liftQ p hker
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨R'.mkQ x, by simp [q]⟩
  calc Module.length O N ≤ Module.length O (N' ⧸ R') := Module.length_le_of_surjective q hq
    _ = (Module.finrank O N' : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := GlobalTheory.T.length_quotient_scalar_mul O N' a
    _ ≤ _ := by
      gcongr

end GlobalTheory
