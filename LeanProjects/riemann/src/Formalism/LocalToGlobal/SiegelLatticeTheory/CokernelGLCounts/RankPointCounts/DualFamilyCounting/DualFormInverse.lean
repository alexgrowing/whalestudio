import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualFLeOfInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions Formalism.L2.SG.Pf.GluedFormOrthogonality
  Formalism.L2.SG.Pf.DualFormInverse

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  have hTop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => form_orth_U hs (hbU i) (hwW j)
  have hq0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  have hqS : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := (isLocUnif (K := K) hK hF h𝔭 hu).mem
    rwa [jι_eq'] at this
  have hA0 : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)
  have hC0 : ∀ j, algebraMap F K (c j) ≠ 0 := fun j => (map_ne_zero _).2 (hwn j).2
  have hGr : ∀ j, glueFam K 𝔭 b a π w τ (Sum.inr j) = w j := fun j => rfl
  have hGl : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hGl0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) =
      algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) := by
    intro i
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring

  have hgg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ ^ 2 *
          (algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i))) := by
    intro i hi
    rw [hGl i hi, form_smul_smul, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), key_ii]
    ring
  have hgw : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_left, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), map_add,
      LinearMap.add_apply, hbw, hwn1, zero_add]
  have hwg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_right, inv_pow (algebraMap F K (π : F)), map_add, hwb, hwn1, zero_add]
  have hww : ∀ j, h (glueFam K 𝔭 b a π w τ (Sum.inr j)) (glueFam K 𝔭 b a π w τ (Sum.inr j)) =
      algebraMap F K (c j) := fun j => by rw [hGr, hwn1]
  have hdiag0 : ∀ i, vF 𝔭 (a i) = 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        algebraMap F K ((a i : 𝓞 F) : F) := fun i hi => by rw [hGl0 i hi, hbn]

  have hoff0 : ∀ i, vF 𝔭 (a i) = 0 → ∀ s, s ≠ Sum.inl i →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 := by
    intro i hi s hs'
    rcases s with i' | j
    · exact glue_inl_inl hs hbU hbo hwW hwo hτ (fun e => hs' (congrArg Sum.inl e))
    · exact hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun h1 => absurd hi h1))
  have hoff : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ s, s ≠ Sum.inl i → s ≠ Sum.inr (τ i) →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 ∧
        h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) = 0 := by
    intro i hi s h1 h2
    rcases s with i' | j
    · have hii : i' ≠ i := fun e => h1 (congrArg Sum.inl e)
      exact ⟨glue_inl_inl hs hbU hbo hwW hwo hτ hii,
        glue_inl_w hbU hwW hwo (fun h3 e => hii (hτ i' i h3 hi e))⟩
    · have hj : j ≠ τ i := fun e => h2 (congrArg Sum.inr e)
      exact ⟨hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun _ e => hj e.symm)), hwo j (τ i) hj⟩
  have hoffw : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → ∀ s, s ≠ Sum.inr j →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr j)) = 0 := by
    intro j hj s hs'
    rcases s with i | j'
    · exact glue_inl_w hbU hwW hwo (fun h3 => hj i h3)
    · exact hwo j' j (fun e => hs' (congrArg Sum.inr e))

  have hpair : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ X Y : K, X ∈ SP K 𝔭 → Y ∈ SP K 𝔭 →
      ∃ κ : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → K, (∀ t, κ t ∈ SP K 𝔭) ∧
        ∀ s, ∑ t, κ t * h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t) =
          if s = Sum.inl i then X else if s = Sum.inr (τ i) then Y else 0 := by
    intro i hi X Y hX hY
    obtain ⟨r, hr, hre⟩ := (mem_noncompactPart_iff hu _ _).1 (hcong i hi)
    rw [jι_eq', map_add] at hre
    have hre' : algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i)) ^ 2 * r := by
      rw [hre]; ring
    have hc := unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    obtain ⟨e1, e2⟩ := pair_solve (X := X) (Y := Y) (pow_ne_zero (vF 𝔭 (a i)) hq0) (hA0 i) hc.1 hre'
    obtain ⟨m1, m2⟩ := pair_coeffs_mem (𝔭 := 𝔭) (X := X) (Y := Y) ((SP K 𝔭).pow_mem hqS _)
      (unit_part hK hF h𝔭 hu (ha0 i)) hc.2 hr hX hY
    obtain ⟨κ, hκS, hκ⟩ := exists_two (Sum.inl_ne_inr (a := i) (b := τ i)) m1 m2
      (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
    refine ⟨κ, hκS, fun s => ?_⟩
    rw [hκ s]
    by_cases h1 : s = Sum.inl i
    · subst h1
      rw [if_pos rfl, hgg i hi, hgw i hi]
      linear_combination e1
    · by_cases h2 : s = Sum.inr (τ i)
      · subst h2
        rw [if_neg h1, if_pos rfl, hwg i hi, hww]
        linear_combination e2
      · rw [if_neg h1, if_neg h2, (hoff i hi s h1 h2).1, (hoff i hi s h1 h2).2]
        ring
  refine dualF_le_of_inv hs hnd _ hTop ?_
  intro u
  rcases u with i | j
  · by_cases hi : vF 𝔭 (a i) = 0
    · have hAi : (algebraMap F K ((a i : 𝓞 F) : F))⁻¹ ∈ SP K 𝔭 := by
        have := unit_part hK hF h𝔭 hu (ha0 i)
        rwa [hi, pow_zero, mul_one] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inl i) hAi
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i
      · subst h1
        rw [if_pos rfl, hdiag0 i hi, inv_mul_cancel₀ (hA0 i)]
      · rw [if_neg h1, hoff0 i hi s h1, mul_zero]
    · obtain ⟨κ, hκS, hκ⟩ := hpair i hi 1 0 (SP K 𝔭).one_mem (SP K 𝔭).zero_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
  · by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨κ, hκS, hκ⟩ := hpair i hi 0 1 (SP K 𝔭).zero_mem (SP K 𝔭).one_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
    · simp only [not_exists, not_and] at hj
      have hCj : (algebraMap F K (c j))⁻¹ ∈ SP K 𝔭 := by
        have := (hunit j hj).2
        rwa [map_inv₀] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inr j) hCj
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inr j
      · subst h1
        rw [if_pos rfl, hww, inv_mul_cancel₀ (hC0 j)]
      · rw [if_neg h1, hoffw j hj s h1, mul_zero]

end Formalism.L2.SG.Pf.Cnt
