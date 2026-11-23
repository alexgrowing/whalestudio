import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.map_part :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (W' : WPres O X R'), (∀ s, W'.z s ∈ maximalIdeal R') → ∀ f : R →ₐ[O] R', (∀ s, f (W.z s) ∈ W'.part (W.wt s)) → ∀ j, ∀ x ∈ W.part j, f x ∈ W'.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ W' hW' f hf j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (f.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal R' := fun s => by
    show f (W.z s) ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hW s
  refine part_closed O X R' W' hW' j _ fun N => ⟨_, ?_, GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) hm N g⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [coeff_truncTotal_eq_ite, hg d hne, ite_self]
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact SetLike.prod_pow_mem_graded W'.part W.wt (fun s => f (W.z s)) d (fun s _ => hf s)
