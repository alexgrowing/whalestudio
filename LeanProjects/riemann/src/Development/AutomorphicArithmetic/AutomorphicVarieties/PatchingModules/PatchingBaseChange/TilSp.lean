import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilQuot
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.equiv_of_ker {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C] (f : A →ₐ[K] B) (g : A →ₐ[K] C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : RingHom.ker f = RingHom.ker g) : ∃ τ : B ≃ₐ[K] C, ∀ a, τ (f a) = g a := by
  refine ⟨((Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans (Ideal.quotientEquivAlgOfEq K h)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg), fun a => ?_⟩
  have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) = Ideal.Quotient.mk _ a := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, this]
  rfl

private theorem UpperTheory.V.Pa.BC.spIdeal_fg {R : Type} [CommRing R] {q n : ℕ} (P : Fin q → Polynomial R)
    (ut : Fin q → Fin n → R) : (spIdeal P ut).FG := by
  refine Submodule.fg_span ?_
  have key : ∀ (S : Type) [CommRing S] (Q : Fin q → Polynomial S), {z | ∃ j k, z = (Q j).coeff k}.Finite := by
    intro S _ Q
    refine ((Set.finite_iUnion fun j => (Q j).coeffs.finite_toSet).insert 0).subset ?_
    rintro z ⟨j, k, rfl⟩
    by_cases h : (Q j).coeff k = 0
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Polynomial.coeff_mem_coeffs h⟩)
  exact key _ _

private theorem UpperTheory.V.Pa.BC.spIdeal_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) :
    (spIdeal P ut).map (MvPowerSeries.map φ) = spIdeal (fun j => (P j).map φ) (fun j i => φ (ut j i)) := by
  have key : ∀ j k, MvPowerSeries.map φ (((∏ i, (Polynomial.X -
      Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)))) -
      (P j).map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R)).coeff k) =
      ((∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (φ (ut j i)) + MvPowerSeries.X (j, i)))) -
      ((P j).map φ).map (MvPowerSeries.C : R' →+* MvPowerSeries (Fin q × Fin n) R')).coeff k := by
    intro j k
    rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, Polynomial.map_map]
    have : (MvPowerSeries.map φ).comp (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) =
        (MvPowerSeries.C : R' →+* MvPowerSeries (Fin q × Fin n) R').comp φ := by
      ext1 a
      simp
    rw [this]
    simp
  unfold spIdeal
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨j, k, rfl⟩, rfl⟩
    exact ⟨j, k, key j k⟩
  · rintro ⟨j, k, rfl⟩
    exact ⟨_, ⟨j, k, rfl⟩, key j k⟩

theorem UpperTheory.V.Pa.BC.til_sp :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (B : Type) [CommRing B] [Algebra O B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), ∃ τ : Til O O' (Sp P ut) ≃ₐ[O'] Sp (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)), (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a) = algebraMap (Til O O' B) _ a) ∧ ∀ j i, τ (Til.ι O O' _ (Sp.u P ut j i)) = Sp.u _ _ j i := by
  intro O O' _ _ _ _ _ B _ _ q n P ut
  obtain ⟨τ0, h1, -, h3, -⟩ := UpperTheory.V.Pa.BC.til_mvps O O' B (Fin q × Fin n)
  obtain ⟨hs, hk⟩ := UpperTheory.V.Pa.BC.til_quot O O' _ (spIdeal P ut) (UpperTheory.V.Pa.BC.spIdeal_fg P ut)
  let f : Til O O' (MvPowerSeries (Fin q × Fin n) B) →ₐ[O'] Til O O' (Sp P ut) :=
    Til.map O' ((Sp.mk P ut).restrictScalars O)
  let g : Til O O' (MvPowerSeries (Fin q × Fin n) B) →ₐ[O']
      Sp (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) :=
    ((Sp.mk _ _).restrictScalars O').comp τ0.toAlgHom
  have hf : Function.Surjective f := hs
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp τ0.surjective
  have hfk : RingHom.ker f = (spIdeal P ut).map (Til.ι O O' _) := hk
  have hI : ((spIdeal P ut).map (Til.ι O O' _)).map τ0.toRingEquiv.toRingHom =
      spIdeal (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) := by
    rw [Ideal.map_map, ← UpperTheory.V.Pa.BC.spIdeal_map]
    congr 1
    exact RingHom.ext h1
  have hfg : RingHom.ker f = RingHom.ker g := by
    rw [hfk]
    ext a
    have e1 : a ∈ RingHom.ker g ↔
        τ0 a ∈ spIdeal (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) :=
      Ideal.Quotient.eq_zero_iff_mem
    rw [e1, ← hI]
    exact (Ideal.apply_mem_of_equiv_iff (f := τ0.toRingEquiv)).symm
  obtain ⟨τ, hτ⟩ := UpperTheory.V.Pa.BC.equiv_of_ker f g hf hg hfg
  refine ⟨τ, fun a => ?_, fun j i => ?_⟩
  · have e : Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a =
        f (Til.map O' (IsScalarTower.toAlgHom O B (MvPowerSeries (Fin q × Fin n) B)) a) := by
      have hc : IsScalarTower.toAlgHom O B (Sp P ut) = ((Sp.mk P ut).restrictScalars O).comp
          (IsScalarTower.toAlgHom O B (MvPowerSeries (Fin q × Fin n) B)) :=
        AlgHom.ext fun b => ((Sp.mk P ut).commutes b).symm
      rw [hc]
      refine PowerSeries.ext fun k => ?_
      show Algebra.TensorProduct.map _ _ (Til.coeff O O' B k a) =
        Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (Til.coeff O O' B k a))
      induction Til.coeff O O' B k a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e, hτ]
    show Sp.mk _ _ (τ0 _) = _
    rw [h3]
    exact (Sp.mk _ _).commutes a
  · have e : Til.ι O O' _ (Sp.u P ut j i) =
        f (Til.ι O O' _ (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))) :=
      (Til.map_ι O' ((Sp.mk P ut).restrictScalars O) (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))).symm
    rw [e, hτ]
    show Sp.mk _ _ (τ0 _) = Sp.mk _ _ _
    rw [h1, map_add, MvPowerSeries.map_C, MvPowerSeries.map_X]
