import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExteriorTensorProductConvolutionCalculus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBoundStatement

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem conv_dirac_sub_sum {G κ : Type} [Group G] [Fintype G] (s : Finset κ) (a : κ → G → ℂ) (b : G → ℂ) (x : G) :
    conv (dirac - ∑ i ∈ s, a i) b x = b x - ∑ i ∈ s, conv (a i) b x := by
  unfold conv dirac
  simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  rw [Finset.sum_eq_single (1 : G)]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem sum_goodSet_le_one (g : ℕ) [Fact g.Prime] (N m : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ) :
    ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤ 1 := by
  have h1 : ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
      ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun F _ _ => ?_
    exact Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  refine h1.trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => sqSet g N) fun _ f => ((torusCard g f : ℝ))⁻¹]
  have h2 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N
  have h3 := mass_nonneg (g := g) N fun _ => True
  simp only [mass, Finset.filter_true] at h2 h3
  exact Finset.prod_le_one (fun _ _ => h3) fun _ _ => h2

theorem badWeight_le : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m q d : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → PrimeOK g q d → (∀ v, IsSeries (τ v)) → ∃ w : ℝ, conv (dirac - eGood τ ch) (tens fun v => (L v).e) 1 = (w : ℂ) * (tens fun v => (L v).e) 1 ∧ w ≤ badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) := by
  intro g _ N m q d ι _ L τ ch hN hP hτ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hg⟩ := hP
  have hS := GlobalTheory.T.goodSquarefreeLabelTuples_weight_ge g N m q d ι ch hN hg ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hS1 := sum_goodSet_le_one g N m ι ch
  have hS0 : 0 ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ :=
    Finset.sum_nonneg fun F _ => Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  choose! w hw1 hw2 using fun v => GlobalTheory.T.series_representation_weight_lower_bound g N (L v) (τ v) (hτ v)
  have hmem : ∀ F ∈ goodSet g N ch, ∀ v, F v ∈ sqSet g N := fun F hF =>
    (good_iff.1 (mem_goodSet_iff_good.1 hF)).1
  refine ⟨1 - ∑ F ∈ goodSet g N ch, ∏ v, w v (F v), ?_, ?_⟩
  · unfold eGood
    rw [conv_dirac_sub_sum]
    push_cast
    rw [sub_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [(tens_calculus ι (GG g N) (GG g N)).1]
    unfold tens
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => hw1 v (F v) (hmem F hF v)
  · have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_le
    have hg0 : (0 : ℝ) < g := by linarith
    have hinv : 1 / (g : ℝ) ≤ 1 := by rw [div_le_one hg0]; exact hg1
    have hinv0 : 0 ≤ 1 / (g : ℝ) := by positivity
    have hA : (1 - 1 / (g : ℝ)) ^ Fintype.card ι * ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
        ∑ F ∈ goodSet g N ch, ∏ v, w v (F v) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun F hF => ?_
      rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun v _ => ?_) fun v _ => hw2 v (F v) (hmem F hF v)
      exact mul_nonneg (by linarith) (inv_nonneg.2 (Nat.cast_nonneg _))
    have hB : 1 - (Fintype.card ι : ℝ) / g ≤ (1 - 1 / (g : ℝ)) ^ Fintype.card ι := by
      have := one_add_mul_le_pow (a := -(1 / (g : ℝ))) (by linarith) (Fintype.card ι)
      rw [← sub_eq_add_neg] at this
      refine le_trans (le_of_eq ?_) this
      ring
    have hC : 0 ≤ (Fintype.card ι : ℝ) / g := by positivity
    have hD := mul_le_mul_of_nonneg_right hB hS0
    have hE := mul_le_mul_of_nonneg_left hS1 hC
    nlinarith

end GlobalTheory.BadShare
