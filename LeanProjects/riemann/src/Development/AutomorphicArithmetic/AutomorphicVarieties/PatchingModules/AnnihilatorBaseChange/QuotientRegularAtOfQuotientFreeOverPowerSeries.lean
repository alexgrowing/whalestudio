import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.KjMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegPS
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegScal
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.quotientRegularAt_of_quotient_free_over_powerSeries :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (M : Type) [AddCommGroup M] [Module R M] (a j r : ℕ) (e : (M ⧸ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)) ≃+ (Fin r → MvPowerSeries σ Λ ⧸ kjIdeal Λ σ (a + 1) j)), (∀ z m, e (s z • m) = z • e m) → QRegAt M (fun a => s (MvPowerSeries.X a)) (((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) a := by
  intro Λ R σ _ _ _ _ s M _ _ a j r e he c hc α
  classical
  rw [← kjMap Λ R σ s (a + 1) j] at hc
  have hsurj := Ideal.Quotient.mk_surjective (I := kjIdeal Λ σ (a + 1) j)
  choose t ht using fun β i => hsurj (e (Submodule.Quotient.mk (c β)) i)
  have hmono : ∀ β : σ →₀ ℕ, GlobalTheory.monoVal (fun a => s (MvPowerSeries.X a)) β =
      s (GlobalTheory.monoVal MvPowerSeries.X β) := fun β => by
    simp only [GlobalTheory.monoVal, Finsupp.prod, map_prod, map_pow]
  have h0 := congrArg e ((Submodule.Quotient.mk_eq_zero _).2 hc)
  rw [map_zero, ← Submodule.mkQ_apply, map_sum, map_sum] at h0
  simp only [map_smul, hmono, he, Submodule.mkQ_apply] at h0
  have hL : ∀ i, t α i ∈ kjIdeal Λ σ 1 j := by
    intro i
    have h1 := congrFun h0 i
    rw [Finset.sum_apply] at h1
    simp only [Pi.smul_apply, ← ht, Pi.zero_apply] at h1
    have h2 : (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ Λ) β.1 * t β i) ∈ kjIdeal Λ σ (a + 1) j := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← h1]
      rfl
    have h3 := qRegAt_mvPowerSeries Λ σ (maximalIdeal Λ ^ j) a (fun β => t β i)
      (by simpa [kjIdeal, Ideal.map_pow] using h2) α
    simpa [kjIdeal, Ideal.map_pow] using h3
  have hs := Submodule.Quotient.mk_surjective ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M)
  choose m hm using fun i : Fin r => hs (e.symm (Pi.single i 1))
  have h4 : c α - ∑ i, s (t α i) • m i ∈ ((kjIdeal Λ σ (a + 1) j).map s • ⊤ : Submodule R M) := by
    rw [← Submodule.Quotient.eq]
    apply e.injective
    rw [← Submodule.mkQ_apply _ (∑ i, _), map_sum, map_sum]
    simp only [map_smul, he, Submodule.mkQ_apply, hm, AddEquiv.apply_symm_apply]
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · rw [← ht, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hle : kjIdeal Λ σ (a + 1) j ≤ kjIdeal Λ σ 1 j := by
    unfold kjIdeal
    exact sup_le_sup_right (Ideal.pow_le_pow_right (by omega)) _
  have h5 : c α ∈ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R M) := by
    rw [← sub_add_cancel (c α) (∑ i, s (t α i) • m i)]
    refine add_mem (Submodule.smul_mono_left (Ideal.map_mono hle) h4) (Submodule.sum_mem _ fun i _ => ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (hL i)) Submodule.mem_top
  rw [kjMap, pow_one] at h5
  exact h5
