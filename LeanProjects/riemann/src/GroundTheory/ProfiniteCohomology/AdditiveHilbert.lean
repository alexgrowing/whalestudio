import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits

universe u

section NormalBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem normalBasis_repr_apply_smul (σ τ : Gal(L/K)) (y : L) :
    (IsGalois.normalBasis K L).repr (σ y) τ = (IsGalois.normalBasis K L).repr y (σ⁻¹ * τ) := by
  have hb (ρ : Gal(L/K)) :
      σ (IsGalois.normalBasis K L ρ) = IsGalois.normalBasis K L (σ * ρ) := by
    rw [IsGalois.normalBasis_apply (σ * ρ), IsGalois.normalBasis_apply ρ, AlgEquiv.mul_apply]
  have key : (Finsupp.lapply τ ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap ∘ₗ σ.toLinearMap :
      L →ₗ[K] K) = Finsupp.lapply (σ⁻¹ * τ) ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap := by
    refine (IsGalois.normalBasis K L).ext fun ρ => ?_
    change (IsGalois.normalBasis K L).repr (σ (IsGalois.normalBasis K L ρ)) τ =
      (IsGalois.normalBasis K L).repr (IsGalois.normalBasis K L ρ) (σ⁻¹ * τ)
    classical
    rw [hb, Module.Basis.repr_self, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  exact LinearMap.congr_fun key y

end NormalBasis

section Coinduced

variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def galoisCoindIso :
    Rep.ofDistribMulAction k Gal(L/K) L ≅
      Rep.coind (⊥ : Subgroup Gal(L/K)).subtype (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) := by
  have htop : (Representation.trivial k (⊥ : Subgroup Gal(L/K)) K).coindV
      (⊥ : Subgroup Gal(L/K)).subtype = ⊤ := by
    ext f
    simp only [Representation.mem_coindV, Submodule.mem_top, iff_true]
    rintro ⟨g, hg⟩ h
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  let e : L ≃ₗ[k] _ :=
    ((IsGalois.normalBasis K L).equivFun.restrictScalars k).trans
      ((LinearEquiv.funCongrLeft k K (Equiv.inv Gal(L/K))).trans (LinearEquiv.ofTop _ htop).symm)
  refine Rep.mkIso (Representation.Equiv.mk e fun σ => ?_)
  refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
  change (IsGalois.normalBasis K L).repr (σ y) h⁻¹ =
    (IsGalois.normalBasis K L).repr y (h * σ)⁻¹
  rw [normalBasis_repr_apply_smul, mul_inv_rev]

end Coinduced

section Vanishing

open groupCohomology

variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

theorem isZero_groupCohomology_succ (n : ℕ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) n).of_iso
    ((groupCohomology.functor k Gal(L/K) (n + 1)).mapIso (galoisCoindIso k K L) ≪≫
      groupCohomology.coindIso _ (n + 1))

theorem isZero_groupCohomology {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_groupCohomology_succ k K L m

theorem isZero_groupCohomology_galois {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) :=
  isZero_groupCohomology K K L hn

theorem subsingleton_groupCohomology_galois {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) :=
  ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_galois K L hn)

theorem isCoboundary₁_of_isCocycle₁_galois (f : Gal(L/K) → L) (hf : IsCocycle₁ f) :
    IsCoboundary₁ f := by
  have := subsingleton_groupCohomology_galois K L one_ne_zero
  have h0 : H1π (Rep.ofDistribMulAction K Gal(L/K) L) (cocyclesOfIsCocycle₁ hf) = 0 :=
    Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at h0
  exact isCoboundary₁_of_mem_coboundaries₁ f h0

end Vanishing

section Integral

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

end Integral

end GroundTheory.ProfCoh
