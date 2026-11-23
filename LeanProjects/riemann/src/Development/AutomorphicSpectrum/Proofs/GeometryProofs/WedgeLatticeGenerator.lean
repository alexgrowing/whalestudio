import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem ιMulti_ne_zero {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (Module.Basis.span hb).equivFun.toLinearMap
  have hφb : ∀ j, φ (b j) = Pi.single j 1 := by
    intro j
    have h2 : φ (b j) = (Module.Basis.span hb).equivFun (Module.Basis.span hb j) := by
      rw [Module.Basis.span_apply hb j]
      exact LinearMap.congr_fun hφ ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩
    rw [h2]
    ext k
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  intro h0
  have h1 := congrArg (exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating (n := Fin r) (R := Ω)).compLinearMap φ)) h0
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at h1
  have h2 : (fun i => φ (b i)) = (1 : Matrix (Fin r) (Fin r) Ω) := by
    ext i j
    simp [hφb, Matrix.one_apply, Pi.single_apply, eq_comm]
  have h3 : Matrix.det (fun i => φ (b i) : Matrix (Fin r) (Fin r) Ω) = 0 := h1
  rw [h2, Matrix.det_one] at h3
  exact one_ne_zero h3

theorem ιMulti_mem_span {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ} (b c : Fin r → E)
    (hc : ∀ i, c i ∈ Submodule.span R (Set.range b)) :
    exteriorPower.ιMulti Ω r c ∈ Submodule.span R {exteriorPower.ιMulti Ω r b} := by
  classical
  choose m hm using fun i => (Submodule.mem_span_range_iff_exists_fun R).1 (hc i)
  have hc' : c = fun i => ∑ j, ((m i j : R) : Ω) • b j := by
    funext i
    rw [← hm i]
    rfl
  have hsum : exteriorPower.ιMulti Ω r (fun i => ∑ j, ((m i j : R) : Ω) • b j) =
      ∑ σ : Fin r → Fin r, exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_sum (fun i j => ((m i j : R) : Ω) • b j)
  rw [hc', hsum]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hsm : exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) =
      (∏ i, ((m i (σ i) : R) : Ω)) • exteriorPower.ιMulti Ω r (b ∘ σ) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_smul_univ _ _
  have hR : (∏ i, ((m i (σ i) : R) : Ω)) ∈ R := prod_mem fun i _ => (m i (σ i)).2
  rw [hsm]
  by_cases hσ : Function.Injective σ
  · have hperm := (exteriorPower.ιMulti Ω r).map_perm b (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))
    have hco : b ∘ (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ)) = b ∘ σ := rfl
    rw [hco] at hperm
    rw [hperm]
    refine Submodule.smul_mem _ (⟨_, hR⟩ : R) ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))) with h | h
    · rw [h, one_smul]
      exact Submodule.mem_span_singleton_self _
    · rw [h, Units.neg_smul, one_smul]
      exact neg_mem (Submodule.mem_span_singleton_self _)
  · have h0 : exteriorPower.ιMulti Ω r (b ∘ σ) = 0 :=
      (exteriorPower.ιMulti Ω r).map_eq_zero_of_not_injective _ fun h => hσ h.of_comp
    rw [h0, smul_zero]
    exact zero_mem _

theorem wedge_eq_span_ιMulti : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p → L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} ∧ exteriorPower.ιMulti Ω r b ≠ 0 := by
  intro X Ω _ ξ E _ _ L r b p ⟨hb, hL⟩
  refine ⟨le_antisymm ?_ ?_, ιMulti_ne_zero hb⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact ιMulti_mem_span (regAt ξ p) b c (fun i => hL ▸ hc i)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨b, fun i => by rw [hL]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame
