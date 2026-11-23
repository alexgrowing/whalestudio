import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem family_gram_holds : FamGram := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hwW j) (b i)) (hbU i))
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => by
    rw [← hs.eq (b i) (w j), hbw]; simp
  have hcP : ∀ i, vF 𝔭 (a i) ≠ 0 → InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K (c (τ i))) := by
    intro i hi
    have h1 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i))) :=
      (hcong i hi).mono (by omega)
    have h2 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : 𝓞 F) : F)) := inP_vF h𝔭 (ha0 i)
    have e : algebraMap F K (c (τ i)) =
        algebraMap F K ((a i : F) + c (τ i)) + -algebraMap F K ((a i : 𝓞 F) : F) := by
      rw [map_add]; ring
    rw [e]; exact h1.add h2.neg
  have hcS : ∀ j, algebraMap F K (c j) ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      exact (hcP i hi).mem_SP
    · push Not at hj
      exact (hunit j fun i hi => hj i hi).1
  have haS : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ∈ SP K 𝔭 := fun i => by
    rw [← jι_eq']; exact jK_mem_SP _
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) = algebraMap F K ((a i : F) + c (τ i)) := by
    intro i
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring
  have key_ik : ∀ i k, i ≠ k → vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 →
      h (b i + w (τ i)) (b k + w (τ k)) = 0 := by
    intro i k hik hi hk
    have hτik : τ i ≠ τ k := fun e => hik (hτ i k hi hk e)
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbo i k hik, hwo _ _ hτik]
    ring
  suffices H : ∀ x y, h (glueFam K 𝔭 b a π w τ x) (glueFam K 𝔭 b a π w τ y) ∈ SP K 𝔭 by
    intro x y; rw [← mem_SP_iff_locF]; exact H x y
  rintro (i | j) (k | l)
  · simp only [glueFam, Sum.elim_inl]
    by_cases hik : i = k
    · subst hik
      by_cases hi : vF 𝔭 (a i) = 0
      · rw [if_pos hi, hbn]; exact haS i
      · rw [if_neg hi, form_smul_smul, key_ii i, star_inv_pow hF, ← pow_add, ← two_mul]
        exact mem_SP_of_inP hu (hcong i hi)
    · by_cases hi : vF 𝔭 (a i) = 0 <;> by_cases hk : vF 𝔭 (a k) = 0
      · rw [if_pos hi, if_pos hk, hbo i k hik]; exact (SP K 𝔭).zero_mem
      · rw [if_pos hi, if_neg hk, form_smul_right, map_add, hbo i k hik, hbw, add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_pos hk, form_smul_left, map_add, LinearMap.add_apply, hbo i k hik, hwb,
          add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_neg hk, form_smul_smul, key_ik i k hik hi hk, mul_zero]
        exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [if_pos hi, hbw]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hi, form_smul_left, map_add, LinearMap.add_apply, hbw, zero_add, star_inv_pow hF]
      by_cases hj : τ i = l
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP i hi)
      · rw [hwo _ _ hj, mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hk : vF 𝔭 (a k) = 0
    · rw [if_pos hk, hwb]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hk, form_smul_right, map_add, hwb, zero_add]
      by_cases hj : τ k = j
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP k hk)
      · rw [hwo _ _ (Ne.symm hj), mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inr]
    by_cases hjl : j = l
    · subst hjl; rw [hwn1]; exact hcS j
    · rw [hwo _ _ hjl]; exact (SP K 𝔭).zero_mem

end Formalism.L2.SG.Pf.GluingBases
