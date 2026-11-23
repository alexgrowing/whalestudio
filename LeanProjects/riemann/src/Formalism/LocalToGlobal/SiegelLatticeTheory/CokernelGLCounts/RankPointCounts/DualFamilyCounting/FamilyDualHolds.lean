import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueInlInl

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem form_sum_orth {ι' : Type} [Fintype ι'] [DecidableEq ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι' → V)
    (hvo : ∀ i k, i ≠ k → h (v i) (v k) = 0) (i : ι') (x : ι' → K) :
    h (v i) (∑ k, x k • v k) = x i * h (v i) (v i) := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_eq_single i (fun k _ hk => by rw [hvo i k (Ne.symm hk), mul_zero]) (by simp)

theorem form_sum_zero {ι' : Type} [Fintype ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (v : ι' → V)
    (h0 : ∀ k, h u (v k) = 0) (x : ι' → K) : h u (∑ k, x k • v k) = 0 := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, h0, mul_zero, Finset.sum_const_zero]

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  have htop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => GluedFormOrthogonality.form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => GluedFormOrthogonality.form_orth_U hs (hbU i) (hwW j)
  have hϖ0 : algebraMap F K (π : F) ≠ 0 := by rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  set L := Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)) with hL
  have hGi : ∀ s, glueFam K 𝔭 b a π w τ s ∈ L := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hGw : ∀ j, w j ∈ L := fun j => hGi (Sum.inr j)
  have hg1 : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hg0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have hGb : ∀ i, b i ∈ L := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [← hg0 i hi]; exact hGi _
    · have e : b i = (algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i)) • glueFam K 𝔭 b a π w τ (Sum.inl i)
          - w (τ i) := by
        rw [hg1 i hi, ← algebraMap_smul K, smul_smul, map_pow, jι_eq', ← mul_pow,
          mul_inv_cancel₀ hϖ0, one_pow, one_smul, add_sub_cancel_right]
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hGi _)) (hGw _)
  intro x hx
  have hX : ∀ z ∈ L, h z x ∈ SP K 𝔭 := fun z hz => by
    rw [mem_SP_iff_locF]; exact hx z (LocF.le_locF 𝔭 _ hz)
  have hbw_top : Submodule.span K (Set.range (Sum.elim b w)) = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rcases s with i | j
    · by_cases hi : vF 𝔭 (a i) = 0
      · rw [hg0 i hi]; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · rw [hg1 i hi]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.subset_span ⟨Sum.inr (τ i), rfl⟩))
    · exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hxmem : x ∈ Submodule.span K (Set.range (Sum.elim b w)) := by
    rw [hbw_top]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxmem
  rw [Fintype.sum_sum_type] at hf
  simp only [Sum.elim_inl, Sum.elim_inr] at hf
  have hbx : ∀ i, h (b i) x = f (Sum.inl i) * algebraMap F K (a i : F) := by
    intro i
    rw [← hf, map_add, form_sum_orth h b hbo i, form_sum_zero h (b i) w (hbw i), hbn, add_zero]
  have hwx : ∀ j, h (w j) x = f (Sum.inr j) * algebraMap F K (c j) := by
    intro j
    rw [← hf, map_add, form_sum_orth h w hwo j, form_sum_zero h (w j) b (fun i => hwb i j),
      (hwn j).1, zero_add]
  have hα : ∀ i, f (Sum.inl i) * algebraMap F K (a i : F) ∈ SP K 𝔭 := fun i => by
    rw [← hbx]; exact hX _ (hGb i)
  have hγ : ∀ j, f (Sum.inr j) * algebraMap F K (c j) ∈ SP K 𝔭 := fun j => by
    rw [← hwx]; exact hX _ (hGw j)
  have hσ : ∀ i, vF 𝔭 (a i) ≠ 0 → (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
      (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i))) ∈
        SP K 𝔭 := by
    intro i hi
    have h1 := hX _ (hGi (Sum.inl i))
    rwa [hg1 i hi, form_smul_left, star_inv_pow hF, map_add, LinearMap.add_apply, hbx, hwx] at h1
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)

  have cf0 : ∀ i, vF 𝔭 (a i) = 0 → f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    rw [hi, pow_zero, mul_one] at hu'
    have e : f (Sum.inl i) = (f (Sum.inl i) * algebraMap F K (a i : F)) *
        (algebraMap F K (a i : F))⁻¹ := by field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf1 : ∀ i, vF 𝔭 (a i) ≠ 0 →
      f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have e : f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) =
        (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf2 : ∀ i, vF 𝔭 (a i) ≠ 0 → f (Sum.inr (τ i)) - f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    obtain ⟨hC0, huc⟩ := UnitPairSolutions.unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    have hua := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have hr := mem_SP_of_inP hu (hcong i hi)
    have hq0 : algebraMap F K (π : F) ^ vF 𝔭 (a i) ≠ 0 := pow_ne_zero _ hϖ0
    have e : f (Sum.inr (τ i)) - f (Sum.inl i) =
        ((algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
          (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i)))) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) -
        ((algebraMap F K (π : F))⁻¹ ^ (2 * vF 𝔭 (a i)) * algebraMap F K ((a i : F) + c (τ i))) *
          (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      rw [map_add, inv_pow, inv_pow, pow_mul]
      field_simp [hA0 i, hC0, hϖ0]
      ring
    rw [e]
    exact (SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem (hσ i hi) huc)
      ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hr (hα i)) hua) huc)
  classical
  set P := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  let z : Fin (finrank K (orthK h U)) → K := fun j =>
    f (Sum.inr j) - ∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)
  have hz : ∀ j, z j ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      have e : ∑ i' ∈ P.filter (fun i' => τ i' = τ i), f (Sum.inl i') = f (Sum.inl i) := by
        apply Finset.sum_eq_single_of_mem
        · simp [hP, hi]
        · intro i' hi' hne
          simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
          exact absurd (hτ i' i hi'.1 hi hi'.2) hne
      show f (Sum.inr (τ i)) - _ ∈ _
      rw [e]; exact cf2 i hi
    · have e : ∑ i' ∈ P.filter (fun i' => τ i' = j), f (Sum.inl i') = 0 := by
        apply Finset.sum_eq_zero
        intro i' hi'
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
        exact absurd ⟨i', hi'.1, hi'.2⟩ hj
      show f (Sum.inr j) - _ ∈ _
      rw [e, sub_zero]
      have h1 := (hunit j (fun i hi e' => hj ⟨i, hi, e'⟩)).2
      rw [map_inv₀] at h1
      have e2 : f (Sum.inr j) = (f (Sum.inr j) * algebraMap F K (c j)) * (algebraMap F K (c j))⁻¹ := by
        field_simp [(map_ne_zero _).2 (hwn j).2]
      rw [e2]; exact (SP K 𝔭).mul_mem (hγ j) h1
  let coef : Fin (finrank K U) → K := fun i => if vF 𝔭 (a i) = 0 then f (Sum.inl i) else
    f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i)
  have hcoef : ∀ i, coef i ∈ SP K 𝔭 := fun i => by
    simp only [coef]; split_ifs with hi
    · exact cf0 i hi
    · exact cf1 i hi
  have hterm : ∀ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) =
      f (Sum.inl i) • b i + (if vF 𝔭 (a i) ≠ 0 then f (Sum.inl i) • w (τ i) else 0) := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · simp only [coef, if_pos hi]
      rw [hg0 i hi, if_neg (fun h' => h' hi), add_zero]
    · simp only [coef, if_neg hi]
      rw [hg1 i hi, if_pos hi, smul_smul, mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow,
        mul_one, smul_add]
  have hfib : ∑ j, (∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)) • w j =
      ∑ i ∈ P, f (Sum.inl i) • w (τ i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.univ) (g := τ)
      (fun i _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hdec : x = ∑ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) + ∑ j, z j • w j := by
    simp only [hterm, Finset.sum_add_distrib, z, sub_smul, Finset.sum_sub_distrib, hfib]
    rw [← Finset.sum_filter]
    conv_lhs => rw [← hf]
    abel
  rw [hdec]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => UnitPairSolutions.smul_mem_locF_of_SP (hcoef i) (hGi _))
    (Submodule.sum_mem _ fun j _ => UnitPairSolutions.smul_mem_locF_of_SP (hz j) (hGw j))

end Formalism.L2.SG.Pf.GluingBases
