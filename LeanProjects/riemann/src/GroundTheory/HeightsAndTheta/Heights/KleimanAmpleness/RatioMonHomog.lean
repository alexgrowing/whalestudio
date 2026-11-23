import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistModNatMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

noncomputable section

section Ratio

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def ResidueGen.ratioMon (β : K → ℤ) (c d : ∀ k, ι k) : MRingOver F ι :=
  ∏ k, (X ⟨k, d k⟩ ^ (β k).toNat * X ⟨k, c k⟩ ^ (-β k).toNat)

theorem ResidueGen.ratioMon_homog (β : K → ℤ) :
    ∃ a : K → ℕ, ∀ c d : ∀ k, ι k, IsMultiHomog (ResidueGen.ratioMon (F := F) β c d) a := by
  classical
  refine ⟨_, fun c d => ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_prod _ _ _ fun k _ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_mul
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (d k)) _)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_pow (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k (c k)) _)⟩

omit [∀ k, Fintype (ι k)] in
theorem ResidueGen.aeval_ratioMon {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) =
      ∏ k, (z ⟨k, d k⟩ ^ (β k).toNat * z ⟨k, c k⟩ ^ (-β k).toNat) := by
  simp [ResidueGen.ratioMon, map_prod]

omit [∀ k, Fintype (ι k)] in

theorem ResidueGen.ratio_eval {L : Type} [Field L] [Algebra F L] (z : (Σ k, ι k) → L) (β : K → ℤ)
    (c d : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hd : ∀ k, z ⟨k, d k⟩ ≠ 0) :
    aeval z (ResidueGen.ratioMon (F := F) β c d) / aeval z (ResidueGen.ratioMon (F := F) β d c) =
      (∏ k, z ⟨k, c k⟩ ^ (-β k)) / ∏ k, z ⟨k, d k⟩ ^ (-β k) := by
  rw [ResidueGen.aeval_ratioMon, ResidueGen.aeval_ratioMon, ← Finset.prod_div_distrib,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hck := hc k
  have hdk := hd k
  conv_rhs => rw [← Int.toNat_sub_toNat_neg (β k)]
  rw [neg_sub, zpow_sub₀ hck, zpow_sub₀ hdk]
  simp only [zpow_natCast]
  field_simp

end Ratio

theorem ResidueGen.proof : ResidueGen.Statement := by
  intro F _ K _ ι _ Ω _ _ y K' _ _ y' _ R σ hσ hchart β hgen d₀ hd₀
  classical

  have hne : ∀ p : Σ k, ι k, y' p ≠ 0 → y p ≠ 0 := by
    rintro ⟨k, a⟩ hp h0
    obtain ⟨hm, he⟩ := hσ (X ⟨k, a⟩) (X ⟨k, a⟩) _ (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a)
      (ReciprocityTheory.ChartRestriction.G.AI.I1.isMultiHomog_X k a) (by simpa [aeval_X] using hp)
    have h0' : (⟨_, hm⟩ : R) = 0 := Subtype.ext (by simp [aeval_X, h0])
    rw [h0', map_zero, aeval_X, div_self hp] at he
    exact zero_ne_one he
  have hy0 : ∀ k, y ⟨k, d₀ k⟩ ≠ 0 := fun k => hne _ (hd₀ k)
  have hG0' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  have hG0 : (∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy0 k)
  obtain ⟨ext, ext_eq⟩ : ∃ e : Ω → K', ∀ z (hz : z ∈ R), e z = σ ⟨z, hz⟩ :=
    ⟨fun z => if hz : z ∈ R then σ ⟨z, hz⟩ else 0, fun z hz => dif_pos hz⟩
  obtain ⟨a, ha⟩ := ResidueGen.ratioMon_homog (F := F) (ι := ι) β

  have key : ∀ h ∈ secOver F y β, ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∃ hh : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R,
        σ ⟨_, hh⟩ = ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) *
          ∏ k, y' ⟨k, c k⟩ ^ (-β k) := by
    intro h hH c hc'
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
    obtain ⟨h0R, -⟩ := hchart d₀ hd₀ _ ((PowRealises.mem_secOver y β h).mp hH d₀ hy0)
    obtain ⟨hrR, hr⟩ := hσ (ResidueGen.ratioMon β c d₀) (ResidueGen.ratioMon β d₀ c) a (ha c d₀) (ha d₀ c)
      (by
        rw [ResidueGen.aeval_ratioMon]
        exact Finset.prod_ne_zero_iff.mpr fun k _ =>
          mul_ne_zero (pow_ne_zero _ (hc' k)) (pow_ne_zero _ (hd₀ k)))
    have eqΩ := ResidueGen.ratio_eval (F := F) y β c d₀ hc hy0
    have eqK := ResidueGen.ratio_eval (F := F) y' β c d₀ hc' hd₀
    have hprod : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) = (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) *
        (aeval y (ResidueGen.ratioMon (F := F) β c d₀) / aeval y (ResidueGen.ratioMon (F := F) β d₀ c)) := by
      rw [eqΩ]
      field_simp
    have hmem : h * ∏ k, y ⟨k, c k⟩ ^ (-β k) ∈ R := by
      rw [hprod]
      exact mul_mem h0R hrR
    refine ⟨hmem, ?_⟩
    have hsplit : (⟨_, hmem⟩ : R) = ⟨_, h0R⟩ * ⟨_, hrR⟩ := Subtype.ext hprod
    rw [hsplit, map_mul, hr, eqK, ext_eq _ h0R]
    ring
  refine ⟨fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)),
    fun h hH => key h hH d₀ hd₀, ?_⟩
  intro c hc'
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hne _ (hc' k)
  have hGc' : (∏ k, y' ⟨k, c k⟩ ^ (-β k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc' k)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨h, hH, rfl⟩
    rw [SetLike.mem_coe, PowRealises.mem_span_inv_iff _ hGc']
    obtain ⟨hh, he⟩ := key h hH c hc'
    obtain ⟨_, hin⟩ := hchart c hc' _ ((PowRealises.mem_secOver y β h).mp hH c hc)
    beta_reduce
    rw [← he]
    exact hin
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hg⟩ := hgen
    obtain ⟨u, hu, hsum⟩ := hg c hc
    choose hUR hUc using fun j => hchart c hc' _ (hu j)
    choose hWR hW using fun j => key (s j) (hs j) c hc'
    have hsumR : (∑ j, (⟨u j, hUR j⟩ : R) * ⟨_, hWR j⟩) = 1 := by
      apply Subtype.ext
      push_cast
      exact hsum
    have hone := congrArg σ hsumR
    rw [map_sum, map_one] at hone
    have h2 : (∑ j, σ ⟨u j, hUR j⟩ *
        (ext (s j * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)))) *
          (∏ k, y' ⟨k, c k⟩ ^ (-β k)) = 1 := by
      rw [Finset.sum_mul, ← hone]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hW j]
      ring
    rw [← eq_inv_of_mul_eq_one_left h2]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hj := Submodule.smul_mem
      (Submodule.span (chartRingOver F y' c)
        ((fun h => ext (h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k)) / (∏ k, y' ⟨k, d₀ k⟩ ^ (-β k))) ''
          (secOver F y β : Set Ω)))
      (⟨_, hUc j⟩ : chartRingOver F y' c) (Submodule.subset_span (Set.mem_image_of_mem _ (hs j)))
    rwa [Subalgebra.smul_def, smul_eq_mul] at hj

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
