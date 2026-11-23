import Formalism.FilteredPoleLength.ReducedBasisBounds.LocalStepLevelsExt
import Formalism.FilteredPoleLength.LocalDescentLevels.LevelsChain
import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepExtOf

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem levelsChain_of_add_one_le (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T : ℕ) (e : ℤ)
    (hep : ∀ z, 1 ≤ ep z) (hT : 1 ≤ T) (hc : 0 ≤ c') (hv : ∀ z, 0 ≤ v z)
    (hν : ∀ z, ν z ≤ νs + c' * v z) (he : (T : ℝ) * νs + 1 ≤ e) :
    ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hf : (0 : ℝ) ≤ f z := Nat.cast_nonneg _
  have hep0 : (1 : ℝ) ≤ ep z := by exact_mod_cast hep z
  have hT0 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hbound : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) ≤ (ep z : ℝ) * T * c' * v z := by
    have hy : 0 ≤ (ep z : ℝ) * T * c' * v z := by
      have := hv z
      positivity
    rw [Int.cast_max, Int.cast_zero]
    apply max_le hy
    have h1 := mul_le_mul_of_nonneg_left (hν z) (by linarith : (0 : ℝ) ≤ T)
    have h2 : (T : ℝ) * ν z - e ≤ T * c' * v z - 1 := by nlinarith
    have h3 : (ep z : ℝ) * ((T : ℝ) * ν z - e) ≤ (ep z) * (T * c' * v z - 1) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 := Int.ceil_lt_add_one ((ep z : ℝ) * ((T : ℝ) * ν z - e))
    nlinarith
  calc ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z
      ≤ (ep z : ℝ) * T * c' * v z * f z := mul_le_mul_of_nonneg_right hbound hf
    _ = T * c' * (((ep z : ℝ) * f z) * v z) := by ring

theorem localLevelsExt : LocalStepLevelsExt := by
  intro ι _ ep f ν v νs c' T R I hep hT hc hv hν O K K₁ V W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 hcase hA hN V'
  have h := localStepExt O K K₁ V W ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3
    h4 h5 h6 ha ha' h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hA) (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hN) h17 V'
  have hAn := ENat.toNat_le_of_le_natCast hA
  have hNn := ENat.toNat_le_of_le_natCast hN
  have hlev : ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - ((e : ℤ) : ℝ))⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z := by
    rcases hcase with h0 | h0
    · exact levelsChain ι ep f ν v νs c' T (e : ℤ) hep hT hc hv hν (Or.inl (by exact_mod_cast h0))
    · exact levelsChain_of_add_one_le ι ep f ν v νs c' T (e : ℤ) hep hT hc hv hν (by exact_mod_cast h0)
  simp only [Int.cast_natCast] at hlev
  have hsumcast : (((∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ)) : ℝ) =
      ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉ : ℤ) : ℝ) * f z := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Nat.cast_mul]
    congr 1
    have h0 : (0 : ℤ) ≤ max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉ := le_max_left _ _
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hRnn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have key : ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ) ≤
      (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) := by
    calc ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ)
        ≤ ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℝ) := by
          exact_mod_cast hAn
      _ ≤ _ := by
          rw [Nat.cast_mul, hsumcast]
          exact mul_le_mul_of_nonneg_left hlev hRnn
  have key2 : ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℝ) ≤ (R : ℝ) * (I : ℝ) := by
    exact_mod_cast hNn
  have hd : (0 : ℝ) ≤ (finrank K K₁ : ℝ) := Nat.cast_nonneg _
  have hR : (finrank K K₁ : ℝ) *
        (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
      (finrank K K₁ : ℝ) * ((e : ℝ) * (finrank K V' : ℝ) +
          ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ) +
          ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℝ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ)) +
        (((IsDiscreteValuationRing.addVal O a).toNat : ℝ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℝ) +
          (finrank K K₁ : ℝ) * (n : ℝ) * (be : ℝ)) := by
    exact_mod_cast h
  have hmul := mul_le_mul_of_nonneg_left (add_le_add key key2) hd
  nlinarith [hR, hmul]

end Formalism.LatticeBaseChangeAlt
