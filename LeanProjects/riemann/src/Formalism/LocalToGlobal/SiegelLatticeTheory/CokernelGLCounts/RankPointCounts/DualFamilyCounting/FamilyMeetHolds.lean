import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocalOfFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.FamilyMeetLattice

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

theorem alg_eq {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (t : 𝓞 F) : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K t).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F K t)
    | simp

theorem family_meet_holds : FamMeet := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  classical
  obtain ⟨hbU, hspan, -, -, -⟩ := hba
  obtain ⟨hwW, hworth, hwc, hτ, ⟨s₀, hu⟩, -, -⟩ := hg
  have hπ0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    intro e0
    exact hu.notMem (by rw [show π = 0 from RingOfIntegers.ext e0]; exact Ideal.zero_mem _)
  set p := algebraMap F K (π : F) with hp
  set G := glueFam K 𝔭 b a π w τ with hG
  have hGl : ∀ i, G (Sum.inl i) = if vF 𝔭 (a i) = 0 then b i else
      ((p)⁻¹ ^ vF 𝔭 (a i)) • (b i + w (τ i)) := fun i => rfl
  have hGr : ∀ j, G (Sum.inr j) = w j := fun j => rfl
  have hUloc : locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
    Formalism.L2.SG.Pf.G7.locF_subspace U h𝔭.isPrime
  apply le_antisymm
  ·
    rintro x ⟨hx, hxU⟩
    rw [← hspan]
    obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).1 hx
    refine (LocF.mem_locF_iff h𝔭.isPrime _ x).2 ⟨t, ht, ?_⟩
    set y := algebraMap (𝓞 F) (𝓞 K) t • x with hy
    have hyU : y ∈ U := Submodule.smul_of_tower_mem U _ hxU
    obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hty
    let cf : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then algebraMap (𝓞 K) K (γ (Sum.inl i)) else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    let co : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then 0 else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    have hz : y - ∑ i, cf i • b i = ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j := by
      rw [← hγ, Fintype.sum_sum_type, add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [hGl, ← algebraMap_smul K (γ (Sum.inl i))]
        simp only [cf, co]
        split_ifs with he
        · rw [zero_smul, sub_self]
        · rw [smul_smul, smul_add]
          abel
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hGr, ← algebraMap_smul K (γ (Sum.inr j))]
    have hzW : ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j ∈ orthK h U :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hwW _))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hwW _))
    have hzU : y - ∑ i, cf i • b i ∈ U :=
      Submodule.sub_mem _ hyU (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbU i))
    have hz0 : y - ∑ i, cf i • b i = 0 :=
      (Submodule.disjoint_def.1 hUc.disjoint) _ hzU (hz ▸ hzW)
    have hint : ∀ i, vF 𝔭 (a i) ≠ 0 → ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = cf i := by
      intro i hi
      have h0 := congrArg (h (w (τ i))) (hz.symm.trans hz0)
      rw [map_zero, map_add, map_sum, map_sum] at h0
      simp only [LinearMap.map_smul, smul_eq_mul] at h0
      rw [Finset.sum_eq_single i, Finset.sum_eq_single (τ i)] at h0
      · have hc := hwc (τ i)
        rw [hc.1, ← add_mul] at h0
        have hc0 : algebraMap F K (c (τ i)) ≠ 0 := by rw [map_ne_zero]; exact hc.2
        have h1 := (mul_eq_zero.1 h0).resolve_right hc0
        refine ⟨-γ (Sum.inr (τ i)), ?_⟩
        simp only [cf, co, if_neg hi] at h1 ⊢
        rw [map_neg]
        linear_combination -h1
      · intro j _ hj
        rw [hworth _ _ (Ne.symm hj), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro i' _ hi'
        simp only [co]
        split_ifs with he
        · rw [zero_mul]
        · rw [hworth _ _ (fun e => hi' (hτ i' i he hi e.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [sub_eq_zero.1 hz0]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases he : vF 𝔭 (a i) = 0
    · have : cf i = algebraMap (𝓞 K) K (γ (Sum.inl i)) := if_pos he
      rw [this, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · obtain ⟨r, hr⟩ := hint i he
      rw [← hr, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  ·
    rw [← hspan]
    refine le_inf (LocF.locF_mono 𝔭 ?_) ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases he : vF 𝔭 (a i) = 0
      · have : G (Sum.inl i) = b i := by rw [hGl, if_pos he]
        exact Submodule.subset_span ⟨Sum.inl i, this⟩
      · have e1 : b i = algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i) • G (Sum.inl i) - G (Sum.inr (τ i)) := by
          rw [hGl, if_neg he, hGr, ← algebraMap_smul K, map_pow, alg_eq, smul_smul, ← mul_pow,
            mul_inv_cancel₀ hπ0, one_pow, one_smul, add_sub_cancel_right]
        rw [e1]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.subset_span ⟨_, rfl⟩)
    · calc locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ≤ locF 𝔭 (U.restrictScalars (𝓞 K)) :=
            LocF.locF_mono 𝔭 (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbU i))
        _ = U.restrictScalars (𝓞 K) := hUloc

end Formalism.L2.SG.Pf.FamilyMeetLattice
