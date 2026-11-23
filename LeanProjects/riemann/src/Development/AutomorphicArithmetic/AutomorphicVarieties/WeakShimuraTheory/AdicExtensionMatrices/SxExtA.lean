import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtGr0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxExtA :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.A →ₐ[Λ] R'), (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz R' _ _ _ f f' hf
  haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ X R W hz
  let ι : ↥(W.gr 0) →ₐ[Λ] W.A :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  have hzA : ∀ s, ((W.zA s : W.A) : R) = W.z s := fun _ => rfl
  have h0 : f.comp ι = f'.comp ι := by
    refine sxExtGr0 W hz R' _ _ ?_
    intro b n _ hb
    have hbA : (b : W.A) = n.prod fun s k => W.zA s ^ k := by
      apply Subtype.ext
      rw [hb]
      simp [Finsupp.prod, hzA]
    show f (b : W.A) = f' (b : W.A)
    rw [hbA]
    simp [Finsupp.prod, map_prod, map_pow, hf]
  refine AlgHom.ext_of_adjoin_eq_top (gr_gen Λ R X W) ?_
  rintro x (hx | ⟨s, rfl⟩)
  · exact congrArg (fun g => g ⟨x, hx⟩) h0
  · exact hf s
