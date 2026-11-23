import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMod

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_quotient_base_change (S T S' : Type) [CommRing S] [CommRing T] [Algebra S T] [CommRing S']
    (τ : T ≃+* S') (I : Ideal S) (rk : ℕ) (M : Type) [AddCommGroup M] [Module S M]
    (e : M ≃ₗ[S] (Fin rk → S ⧸ I)) (I' : Ideal S')
    (hI : I' = I.map ((τ : T →+* S').comp (algebraMap S T))) :
    ∃ e' : T ⊗[S] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (z • m) = τ z • e' m := by
  let J : Ideal T := I.map (algebraMap S T)
  have hJ : I' = J.map (τ : T →+* S') := by
    rw [hI, Ideal.map_map]
  let q : T ⧸ J ≃+* S' ⧸ I' := Ideal.quotientEquiv J I' τ hJ
  let A1 : T ⊗[S] M ≃ₗ[T] T ⊗[S] (Fin rk → S ⧸ I) := LinearEquiv.baseChange S T M _ e
  let A2 : T ⊗[S] (Fin rk → S ⧸ I) ≃ₗ[T] (Fin rk → T ⊗[S] (S ⧸ I)) :=
    (Algebra.TensorProduct.piRight S T T (fun _ : Fin rk => S ⧸ I)).toLinearEquiv
  let A3 : (Fin rk → T ⊗[S] (S ⧸ I)) ≃ₗ[T] (Fin rk → T ⧸ J) :=
    LinearEquiv.piCongrRight (fun _ => (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv)
  let A := (A1.trans A2).trans A3
  refine ⟨A.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => q.toAddEquiv), ?_⟩
  intro z m
  funext i
  change q ((A (z • m)) i) = τ z • q ((A m) i)
  rw [A.map_smul, Pi.smul_apply]
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (A m i)
  rw [← hx, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, ← map_mul, map_mul]

theorem UpperTheory.V.Pa.BC.free_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (s : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] (I : Ideal S) (rk : ℕ) (e : M ≃+ (Fin rk → S ⧸ I)), (∀ z m, e (s z • m) = z • e m) → ∀ (S' : Type) [CommRing S'] (τ : Til O O' S ≃+* S') (I' : Ideal S'), I' = I.map ((τ : Til O O' S →+* S').comp (Til.ι O O' S)) → ∃ e' : Til O O' R ⊗[R] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (Til.map O' s z • m) = τ z • e' m := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ s M _ _ I rk e he S' _ τ I' hI
  letI : Module S M := Module.compHom M s.toRingHom
  let eL : M ≃ₗ[S] (Fin rk → S ⧸ I) := e.toLinearEquiv (fun c x => he c x)
  haveI : Module.Finite S M := Module.Finite.equiv eL.symm
  obtain ⟨ε, -, hε⟩ := BC.til_mod O O' S R s M (fun a m => rfl)
  obtain ⟨f, hf⟩ := free_quotient_base_change S (Til O O' S) S' τ I rk M eL I' (by rw [Til.algebraMap_eq]; exact hI)
  refine ⟨ε.symm.trans f, ?_⟩
  intro z m
  have hsymm : ε.symm (Til.map O' s z • m) = z • ε.symm m := by
    apply ε.injective
    rw [hε, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rw [AddEquiv.trans_apply, hsymm, hf, AddEquiv.trans_apply]
