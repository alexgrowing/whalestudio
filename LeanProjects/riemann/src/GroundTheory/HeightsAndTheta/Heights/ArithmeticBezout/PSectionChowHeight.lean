import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionChowHeight
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecQOfRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ArchOfPlacesEmbedding
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)

namespace SectionChowHeight

variable {n : ℕ}

theorem logMean_C (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (k : ℕ) (z : ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (k + 1))
      (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ) = Real.log ‖z‖ := by
  have h := ObjectsHeight.mahler_eq_chowMean S hS (ObjectsHeight.ofPointMatrix S hS)
    (ObjectsHeight.ofPointMatrix_norm S hS) (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ)
  rw [mahler_C] at h
  exact h.symm

theorem chowHeight_C (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (e : ℕ) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0 = 0 := by
  have hsub := ChowHeightCycleEq.chowHt_sub (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (e + 1))
    (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw 1 (e + 1)) (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0
  simp only [map_C, logMean_C S hS, logMean_C 1 isUnit_one, sub_self, mul_zero,
    Finset.sum_const_zero, zero_div] at hsub
  have hstd : ∀ (σ : ℚ →+* ℂ) (v : Fin n → ℂ),
      ((ArchData.std ℚ n).normAt σ).norm v = IndefiniteRowSideFullHecke.ArithBezout.formNorm 1 v := fun σ v => by
    simp only [ArchData.std]
    rw [ObjectsHeight.std_eq_ofPointMatrix_one, ObjectsHeight.ofPointMatrix_norm]
  have h1 := ObjectsHeight.chowHt_eq_chowHeight (ArchData.std ℚ n) 1 isUnit_one hstd
    (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) (δ := 0)
  rw [chowHeightConst ℚ n (e + 1) _ a ha] at h1
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h1 ⊢
  linarith

theorem chowHeight_C_mul_cycle (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) {e : ℕ} {ι : Type}
    (Z : ι →₀ ℕ) (g : ι → MvPolynomial (Fin (e + 1) × Fin n) ℚ) (d : ι → ℕ)
    (hg : ∀ i ∈ Z.support, g i ≠ 0) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a * ∏ i ∈ Z.support, g i ^ Z i) (∑ i ∈ Z.support, Z i * d i) =
      ∑ i ∈ Z.support, (Z i : ℝ) * IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g i) (d i) := by
  have hMul : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul
  have hne : ∏ i ∈ Z.support, g i ^ Z i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i hi)
  have hadd := ChowHeightCycleEq.additive hMul (fun _ : InfinitePlace ℚ => S) (fun _ => hS)
    (C a) (∏ i ∈ Z.support, g i ^ Z i) 0 (∑ i ∈ Z.support, Z i * d i) (C_ne_zero.mpr ha) hne
  have hcyc := ChowHeightCycleEq.cycle_of_A hMul ℚ n e (fun _ => S) (fun _ => hS) ι Z g d hg
  rw [zero_add] at hadd
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight
  rw [hadd]
  have h0 := chowHeight_C S hS e ha
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h0
  rw [h0, zero_add]
  exact hcyc

end SectionChowHeight

open Classical in

theorem SectionChowHeight.proof (hSec : ChowFormSection.Statement) : SectionChowHeight.Statement := by
  intro n e δ S P f u g d hS hP hf hu hg
  set s := IndefiniteRowSideFullHecke.ArithBezout.linForm u
  have hcyc : IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) (e + 1)
      (specFirst f fun j => (u j : ℚ)) :=
    hSec ℚ n (e + 1) (ObjectsChow.genericIdeal P) f _
      (VerticalPartGauss.isProjPrime_genericIdeal hP) (VerticalPartGauss.isChowForm_genericIdeal hP hf)
      (VerticalPartGauss.linForm_not_mem_genericIdeal hP hu)
  set Zh := (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).filter IsHorizontal with hZh
  have hmem : ∀ W ∈ Zh.support, W ∈ divSupp P s ∧ IsHorizontal W := by
    intro W hW
    rw [hZh, Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff,
      RecQOfRecursion.divCycle_apply] at hW
    exact ⟨by_contra fun h => hW.1 (if_neg h), hW.2⟩
  have hgA : ∀ W ∈ Zh.support, IsChowForm (ObjectsChow.genericIdeal W) (e + 1) (g W) := fun W hW =>
    VerticalPartGauss.isChowForm_genericIdeal
      (ObjectsChow.DivSuppHorizontalArithVar.proof n (e + 1) P u W hP hu (hmem W hW).1 (hmem W hW).2)
      (hg W (hmem W hW).1 (hmem W hW).2)
  have hsfne := RecQOfRecursion.ne_zero_of_isChowFormCycle hcyc
  obtain ⟨c, hc, g', hg', hsf⟩ := hcyc
  have hD := ObjectsChow.DivCycleGeneric.proof n (e + 1) P u hP hu
  rw [hD] at hsf hg'
  have hpos : ∀ W ∈ Zh.support,
      ObjectsChow.genericIdeal W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support := by
    intro W hW
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain, Finsupp.sum_apply]
    have h1 := Finset.single_le_sum (f := fun a => Finsupp.single (ObjectsChow.genericIdeal a) (Zh a)
      (ObjectsChow.genericIdeal W)) (fun _ _ => Nat.zero_le _) hW
    simp only [Finsupp.single_eq_same] at h1
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)) h1).ne'
  have hr : ∀ W ∈ Zh.support, ∃ r : ℚ, r ≠ 0 ∧ g' (ObjectsChow.genericIdeal W) = C r * g W :=
    fun W hW => RecQOfRecursion.exists_C_mul_of_isChowForm (hgA W hW) (hg' _ (hpos W hW))
  choose! r hr0 hr using hr
  have hsf' : specFirst f (fun j => (u j : ℚ)) =
      C (c * ∏ W ∈ Zh.support, r W ^ Zh W) * ∏ W ∈ Zh.support, g W ^ Zh W := by
    have hprod : ∏ W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support,
        g' W ^ (Zh.mapDomain ObjectsChow.genericIdeal) W =
          Zh.prod fun W m => g' (ObjectsChow.genericIdeal W) ^ m :=
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    rw [hsf, hprod, Finsupp.prod, Finset.prod_congr rfl (fun W hW =>
      show g' (ObjectsChow.genericIdeal W) ^ Zh W = C (r W ^ Zh W) * g W ^ Zh W by
        rw [hr W hW, mul_pow, map_pow]), Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]
  have hgne : ∀ W ∈ Zh.support, g W ≠ 0 := fun W hW => (hgA W hW).1
  have hgm : ∀ W ∈ Zh.support, IsMultiHomog (d W) (g W) := fun W hW =>
    ObjectsChow.isMultiHomog_of_isChowForm (hg W (hmem W hW).1 (hmem W hW).2)
  have hc' : c * ∏ W ∈ Zh.support, r W ^ Zh W ≠ 0 :=
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hr0 W hW))
  have hδ : δ = ∑ W ∈ Zh.support, Zh W * d W := by
    have h1 : IsMultiHomog δ (specFirst f fun j => (u j : ℚ)) :=
      (ObjectsChow.isMultiHomog_of_isChowForm hf).specFirst _
    have h2 : IsMultiHomog (∑ W ∈ Zh.support, Zh W * d W) (specFirst f fun j => (u j : ℚ)) := by
      rw [hsf']
      unfold IsMultiHomog
      have := (isWeightedHomogeneous_C (groupWeight (e + 1) n) (c * ∏ W ∈ Zh.support, r W ^ Zh W)).mul
        (IsWeightedHomogeneous.prod Zh.support (fun W => g W ^ Zh W)
          (fun W => Zh W • fun _ : Fin (e + 1) => d W) fun W hW => (hgm W hW).pow (Zh W))
      convert this using 1
      funext i
      simp [Finset.sum_apply]
    exact congrFun (IsWeightedHomogeneous.inj_right hsfne h1 h2) 0
  rw [← ObjectsChow.specFirst_eq, hsf', hδ,
    SectionChowHeight.chowHeight_C_mul_cycle S hS Zh g d hgne hc']
  rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
  refine (Finset.sum_subset (fun W hW => (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mpr
    (hmem W hW).1) ?_).trans (Finset.sum_congr rfl fun W hW => ?_)
  · intro W _ hW
    rw [Finsupp.mem_support_iff, not_not] at hW
    rw [hW, Nat.cast_zero, zero_mul]
  · have hWd : W ∈ divSupp P s := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mp hW
    rw [hZh, Finsupp.filter_apply, RecQOfRecursion.divCycle_apply, if_pos hWd]
    split_ifs <;> simp

end GroundTheory.Heights₂.Heights
