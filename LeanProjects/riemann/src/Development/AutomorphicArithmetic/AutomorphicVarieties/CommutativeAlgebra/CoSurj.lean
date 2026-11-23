import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.RingTheory.AdicCompletion.Functoriality

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_surj :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), maximalIdeal R' ≤ (maximalIdeal R).map f ⊔ maximalIdeal R' ^ 2 → Function.Surjective f := by
  intro O _ _ R _ _ _ R' _ _ _ f hf
  have hle : (maximalIdeal R).map f ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O R', res_map, res_eq_zero_iff]
    exact hx
  have heq : (maximalIdeal R).map (f : R →+* R') = maximalIdeal R' := by
    refine le_antisymm hle ?_
    have hfg : (maximalIdeal R').FG := IsNoetherian.noetherian _
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson _) ?_
    rw [smul_eq_mul, ← pow_two]
    exact hf
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  haveI : IsHausdorff ((maximalIdeal R).map (f : R →+* R')) R' := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal R) (f : R →+* R')
  intro y
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y0
  refine ⟨algebraMap O R a, ?_⟩
  show Ideal.Quotient.mk _ ((f : R →+* R') (algebraMap O R a)) = Ideal.Quotient.mk _ y0
  rw [Ideal.Quotient.eq, heq, AlgHom.coe_toRingHom, AlgHom.commutes, ← neg_sub]
  exact neg_mem ha
