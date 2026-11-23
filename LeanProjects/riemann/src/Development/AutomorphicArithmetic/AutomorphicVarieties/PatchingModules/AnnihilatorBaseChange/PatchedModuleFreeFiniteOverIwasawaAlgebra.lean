import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tens_free {Λ B S M X : Type} [CommRing Λ] [CommRing B] [CommRing S] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Free B S] [Module.Finite B S]
    [Module.Free Λ M] [Module.Finite Λ M] [Nontrivial B] [AddCommGroup X] [Module Λ X]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (e : X ≃+ S ⊗[B] M)
    (he : ∀ (a : Λ) (x : X), e (a • x) = algebraMap B S (lam a) • e x) :
    Module.Free Λ X ∧ Module.Finite Λ X := by
  classical
  let φ : S ⊗[B] M ≃ₗ[B] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    (TensorProduct.congr (Module.Free.chooseBasis B S).repr (LinearEquiv.refl B M)).trans
      (TensorProduct.finsuppScalarLeft B M _)
  have key : ∀ (a : Λ) (x : X), φ (e (a • x)) = a • φ (e x) := by
    intro a x
    rw [he, algebraMap_smul, map_smul]
    ext i
    simp only [Finsupp.smul_apply, hl]
  let ψ : X ≃ₗ[Λ] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    { toFun := fun x => φ (e x)
      invFun := fun f => e.symm (φ.symm f)
      map_add' := fun x y => by simp
      map_smul' := key
      left_inv := fun x => by simp
      right_inv := fun f => by simp }
  exact ⟨Module.Free.of_equiv ψ.symm, Module.Finite.equiv ψ.symm⟩

theorem UpperTheory.V.Pa.Core.patchedModule_free_finite_over_iwasawaAlgebra :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → Module.Free (abelian₂ O Unit D) (X0 m) ∧ Module.Finite (abelian₂ O Unit D) (X0 m) ∧ (∀ (a : abelian₂ O Unit D) (x : X0 m), a • x = m.s.toRingHom (MvPowerSeries.C a) • x) ∧ ∀ p (x : X0 m), m.s.toRingHom (MvPowerSeries.X p) • x = 0 := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT
  obtain ⟨⟨hco, hfree, hfin, -⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hT
  haveI := A.b.free
  haveI := A.b.fin
  haveI := hfree
  haveI := hfin
  have hs : ∀ (t : W.R) (x : X0 m), t • x = m.π t • x := fun _ _ => rfl
  obtain ⟨h1, h2⟩ := tens_free (Λ := abelian₂ O Unit D) (X := X0 m) A.b.lam A.b.smul_lam (AddEquiv.refl _)
    (fun a x => X0.lam_smul_def m a x)
  refine ⟨h1, h2, fun a x => ?_, fun p x => ?_⟩
  · rw [X0.lam_smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s,
      MvPowerSeries.constantCoeff_C]
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s, MvPowerSeries.constantCoeff_X,
      map_zero, map_zero, zero_smul]
