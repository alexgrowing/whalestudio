import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] {A S S' : Type} [CommRing A] [CommRing S] [CommRing S']
  [Algebra R A] [Algebra R S] [Algebra R S'] (I a : Ideal R) (M : Type) [AddCommGroup M] [Module R M]

private theorem UpperTheory.V.Pa.Core.spCong_killI (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (s : S)
    (hs : s ∈ I.map (algebraMap R S)) (w : S ⊗[R] M) :
    s • w ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
  have h1 : ∀ m ∈ (a • ⊤ : Submodule R M), ∀ t : S,
      t ⊗ₜ[R] m ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
    intro m hm t
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr m _
      rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
  have h2 : ∀ i ∈ I, ∀ w : S ⊗[R] M,
      algebraMap R S i • w ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)) := by
    intro i hi w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      exact h1 _ (hI (Submodule.smul_mem_smul hi Submodule.mem_top)) t
    | add x y hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact h2 i hi w
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_smul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, mul_smul]
    exact Submodule.smul_mem _ _ hx

private theorem UpperTheory.V.Pa.Core.spCong_map (f : A →ₐ[R] S) (J : Ideal R) :
    (J.map (algebraMap R A)).map (f : A →+* S) = J.map (algebraMap R S) := by
  rw [Ideal.map_map, AlgHom.comp_algebraMap]

private theorem UpperTheory.V.Pa.Core.spCong_kill (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S) (z : A)
    (hz : z ∈ RingHom.ker f ⊔ I.map (algebraMap R A))
    (x : (S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) : f z • x = 0 := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine UpperTheory.V.Pa.Core.spCong_killI I a M hI _ ?_ w
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add, (RingHom.mem_ker).1 hb, zero_add, ← UpperTheory.V.Pa.Core.spCong_map f I]
  exact Ideal.mem_map_of_mem (f : A →+* S) hc

private theorem UpperTheory.V.Pa.Core.spCong_smul (f : A →ₐ[R] S) (z : A) (x : A ⊗[R] M) :
    f.toLinearMap.rTensor M (z • x) = f z • f.toLinearMap.rTensor M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem UpperTheory.V.Pa.Core.spCong_ker (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S)
    (f' : A →ₐ[R] S') (hf : Function.Surjective f)
    (hk : RingHom.ker f ≤ RingHom.ker f' ⊔ I.map (algebraMap R A)) (x : A ⊗[R] M)
    (hx : f.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) :
    f'.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
  have hF : Function.Surjective (f.toLinearMap.rTensor M) := LinearMap.rTensor_surjective M hf
  have h1 : ∀ y ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M)), ∃ x, f.toLinearMap.rTensor M x = y ∧
      f'.toLinearMap.rTensor M x ∈ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro s hs w _
      rw [← UpperTheory.V.Pa.Core.spCong_map f a] at hs
      obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : A →+* S) hf).1 hs
      obtain ⟨x, rfl⟩ := hF w
      refine ⟨z • x, UpperTheory.V.Pa.Core.spCong_smul M f z x, ?_⟩
      rw [UpperTheory.V.Pa.Core.spCong_smul]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [← UpperTheory.V.Pa.Core.spCong_map f' a]
      exact Ideal.mem_map_of_mem (f' : A →+* S') hz
    · rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
      exact ⟨x + y, map_add _ _ _, by rw [map_add]; exact Submodule.add_mem _ hx hy⟩
  have h2 : ∀ w : (LinearMap.ker f.toLinearMap) ⊗[R] M,
      f'.toLinearMap.rTensor M ((LinearMap.ker f.toLinearMap).subtype.rTensor M w) ∈
        (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      have h := UpperTheory.V.Pa.Core.spCong_kill I a M hI f' t (hk t.2) (Submodule.Quotient.mk (1 ⊗ₜ[R] m))
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      simpa [TensorProduct.smul_tmul'] using h
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
  obtain ⟨x', hx', hm⟩ := h1 _ hx
  have hex := rTensor_exact M (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  obtain ⟨w, hw⟩ := (hex (x - x')).1 (by rw [map_sub, hx', sub_self])
  have h3 := h2 w
  rw [hw, map_sub] at h3
  simpa using Submodule.add_mem _ h3 hm

private theorem UpperTheory.V.Pa.Core.spCong_gen (hI : (I • ⊤ : Submodule R M) ≤ a • ⊤) (f : A →ₐ[R] S)
    (f' : A →ₐ[R] S') (hf : Function.Surjective f) (hf' : Function.Surjective f')
    (hk : RingHom.ker f ≤ RingHom.ker f' ⊔ I.map (algebraMap R A))
    (hk' : RingHom.ker f' ≤ RingHom.ker f ⊔ I.map (algebraMap R A)) :
    ∃ κ : ((S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) ≃+
      ((S' ⊗[R] M) ⧸ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))),
      ∀ z x, κ (f z • x) = f' z • κ x := by
  let φ : A ⊗[R] M →+ ((S ⊗[R] M) ⧸ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] M))) :=
    (Submodule.mkQ _).toAddMonoidHom.comp (f.toLinearMap.rTensor M).toAddMonoidHom
  let φ' : A ⊗[R] M →+ ((S' ⊗[R] M) ⧸ (a.map (algebraMap R S') • ⊤ : Submodule S' (S' ⊗[R] M))) :=
    (Submodule.mkQ _).toAddMonoidHom.comp (f'.toLinearMap.rTensor M).toAddMonoidHom
  have e : ∀ x, φ x = Submodule.Quotient.mk (f.toLinearMap.rTensor M x) := fun _ => rfl
  have e' : ∀ x, φ' x = Submodule.Quotient.mk (f'.toLinearMap.rTensor M x) := fun _ => rfl
  have hφ : Function.Surjective φ :=
    (Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f.toLinearMap) hf)
  have hφ' : Function.Surjective φ' :=
    (Submodule.Quotient.mk_surjective _).comp (LinearMap.rTensor_surjective M (g := f'.toLinearMap) hf')
  have hker : φ.ker = φ'.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, e, e', Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨UpperTheory.V.Pa.Core.spCong_ker I a M hI f f' hf hk x, UpperTheory.V.Pa.Core.spCong_ker I a M hI f' f hf' hk' x⟩
  let κ := ((QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)).trans (QuotientAddGroup.quotientKerEquivOfSurjective φ' hφ')
  have hκ : ∀ x, κ (φ x) = φ' x := by
    intro x
    have : (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) = QuotientAddGroup.mk x := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    simp only [κ, AddEquiv.trans_apply, this]
    rfl
  refine ⟨κ, fun z x => ?_⟩
  obtain ⟨x, rfl⟩ := hφ x
  have h1 : f z • φ x = φ (z • x) := by
    rw [e, e, UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]
  rw [h1, hκ, hκ, e', e', UpperTheory.V.Pa.Core.spCong_smul, Submodule.Quotient.mk_smul]

private theorem UpperTheory.V.Pa.Core.spCong_ideal {q n : ℕ} (P P' : Fin q → Polynomial R) (ut : Fin q → Fin n → R)
    (h : ∀ j k, (P' j).coeff k - (P j).coeff k ∈ I) :
    spIdeal P ut ≤ spIdeal P' ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) := by
  unfold spIdeal
  rw [Ideal.span_le]
  rintro _ ⟨j, k, rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Ideal.subset_span ⟨j, k, rfl⟩, _, Ideal.mem_map_of_mem _ (h j k), ?_⟩
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, map_sub]
  ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Core.spCong :
    ∀ (R : Type) [CommRing R] (q n : ℕ) (P P' : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (I a : Ideal R) (M : Type) [AddCommGroup M] [Module R M], (∀ j k, (P j).coeff k - (P' j).coeff k ∈ I) → (I • ⊤ : Submodule R M) ≤ a • ⊤ → ∃ κ : ((Sp P ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P ut)) • ⊤ : Submodule (Sp P ut) (Sp P ut ⊗[R] M))) ≃+ ((Sp P' ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P' ut)) • ⊤ : Submodule (Sp P' ut) (Sp P' ut ⊗[R] M))), (∀ z x, κ (Sp.mk P ut z • x) = Sp.mk P' ut z • κ x) ∧ ∀ z ∈ spIdeal P ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R), ∀ x : (Sp P ut ⊗[R] M) ⧸ (a.map (algebraMap R (Sp P ut)) • ⊤ : Submodule (Sp P ut) (Sp P ut ⊗[R] M)), Sp.mk P ut z • x = 0 := by
  intro R _ q n P P' ut I a M _ _ h hI
  have hk : ∀ Q : Fin q → Polynomial R, RingHom.ker (Sp.mk Q ut) = spIdeal Q ut := fun Q =>
    Ideal.Quotient.mkₐ_ker R (spIdeal Q ut)
  have hs : ∀ Q : Fin q → Polynomial R, Function.Surjective (Sp.mk Q ut) := fun Q =>
    Ideal.Quotient.mkₐ_surjective R (spIdeal Q ut)
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) =
      algebraMap R (MvPowerSeries (Fin q × Fin n) R) := by
    ext1 r
    simp [MvPowerSeries.algebraMap_apply]
  have h' : ∀ j k, (P' j).coeff k - (P j).coeff k ∈ I := fun j k => by
    rw [← neg_sub]
    exact I.neg_mem (h j k)
  obtain ⟨κ, hκ⟩ := UpperTheory.V.Pa.Core.spCong_gen I a M hI (Sp.mk P ut) (Sp.mk P' ut) (hs P) (hs P')
    (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P P' ut h')
    (by rw [hk, hk, ← hC]; exact UpperTheory.V.Pa.Core.spCong_ideal I P' P ut h)
  refine ⟨κ, hκ, fun z hz x => UpperTheory.V.Pa.Core.spCong_kill I a M hI _ z ?_ x⟩
  rw [hk, ← hC]
  exact hz
