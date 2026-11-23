import Mathlib
open scoped TensorProduct

namespace GlobalTheory

theorem baseChange_inf_lattice_eq_subspace : ∀ {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (N : Submodule O V),
    Submodule.span (FractionRing O) (N : Set V) = ⊤ → ∀ (W : Submodule (FractionRing O) V),
    ∃ e : FractionRing O ⊗[O] ↥(N ⊓ W.restrictScalars O) →ₗ[FractionRing O] V,
      Function.Injective e ∧ LinearMap.range e = W ∧
      ∀ (c : FractionRing O) (x : ↥(N ⊓ W.restrictScalars O)), e (c ⊗ₜ[O] x) = c • (x : V) := by
  intro O V _ _ _ _ _ _ N hN W
  set K := FractionRing O
  have hV : IsBaseChange K (LinearMap.id : V →ₗ[O] V) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).1
      (isLocalizedModule_id (nonZeroDivisors O) V K)
  have hVt : ∀ (c : K) (v : V), hV.equiv (c ⊗ₜ[O] v) = c • v := fun c v => by
    rw [IsBaseChange.equiv_tmul]; rfl

  let fN : K ⊗[O] N →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N.subtype.baseChange K
  have hfN : ∀ y : N, fN (1 ⊗ₜ y) = y := fun y => by simp [fN, hVt]
  have hinjN : Function.Injective fN := hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N.subtype N.injective_subtype)
  have hsurjN : Function.Surjective fN := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hN, Submodule.span_le]
    exact fun y hy => ⟨1 ⊗ₜ ⟨y, hy⟩, hfN _⟩
  have hbN : IsBaseChange K N.subtype :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective fN ⟨hinjN, hsurjN⟩) (fun y => hfN y)
  haveI hlN : IsLocalizedModule (nonZeroDivisors O) N.subtype :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K N.subtype).2 hbN

  set N' := N ⊓ W.restrictScalars O
  let e : K ⊗[O] N' →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N'.subtype.baseChange K
  have het : ∀ (c : K) (x : N'), e (c ⊗ₜ[O] x) = c • (x : V) := fun c x => by
    simp [e, hVt]
  refine ⟨e, hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N'.subtype N'.injective_subtype), ?_, het⟩
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => rw [het]; exact W.smul_mem c x.2.2
    | add a b ha hb => rw [map_add]; exact W.add_mem ha hb
  · intro v hv
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalizedModule.surj (nonZeroDivisors O) N.subtype v
    have hdv : (d : O) • v = (n : V) := hd
    have hdK : (d : O) • v = algebraMap O K d • v := (algebraMap_smul K (d : O) v).symm
    have hW : (n : V) ∈ W := by rw [← hdv, hdK]; exact W.smul_mem _ hv
    have hne : algebraMap O K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    refine ⟨(algebraMap O K d)⁻¹ ⊗ₜ[O] (⟨n, n.2, hW⟩ : N'), ?_⟩
    rw [het]
    show (algebraMap O K d)⁻¹ • (n : V) = v
    rw [← hdv, hdK, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory
