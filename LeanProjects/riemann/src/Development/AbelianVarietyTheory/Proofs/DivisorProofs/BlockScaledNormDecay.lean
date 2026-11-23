import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.MajCompare

theorem evI_add' (F : Type) [Field F] [NumberField F] (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul' (F : Type) [Field F] [NumberField F] (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_one' (F : Type) [Field F] [NumberField F] : evI F (1 : AF F) = 1 :=
  map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_prod' (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (f : ι → AF F) :
    evI F (∏ i ∈ s, f i) = ∏ i ∈ s, evI F (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evI_one']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, evI_mul', ih]

theorem evI_tAd (F : Type) [Field F] [NumberField F] (s : ℝ) :
    evI F (tAd F s) = algebraMap ℝ (mixedEmbedding.mixedSpace F) s := by
  have h : evI F (realAd F (s - 1)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (s - 1) := by
    simp [evI, realAd]
  rw [tAd, evI_add', evI_one', h, map_sub, map_one]; ring

theorem evI_algMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

theorem evI_blkScale (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ}
    (blk : Fin q → Finset κ) (t : Fin q → ℝ) (ξ : κ → F) (j : κ) :
    evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) =
      (∏ i, if j ∈ blk i then t i else 1) • mixedEmbedding F (ξ j) := by
  simp only [blkScale]
  rw [evI_mul', evI_prod', evI_algMap, Algebra.smul_def, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rw [evI_tAd]
  · rw [evI_one', map_one]

end GlobalTheory.ThKTorus.MajCompare

namespace GlobalTheory.ThKTorus.MajCompare

theorem weight_le_majorant : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) → ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ ξ : κ → F,
      ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) ^ ((q + 1) * N))⁻¹ ≤
        C * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
          (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹ := by
  intro F _ _ κ _ _ q blk hdis c hc N
  set m : ℝ := min c 1 with hm_def
  have hm0 : 0 < m := lt_min hc one_pos
  refine ⟨(m ^ N)⁻¹, inv_nonneg.2 (pow_nonneg hm0.le N), ?_⟩
  intro t ht ξ
  set r : κ → ℝ := fun j => ∏ i, if j ∈ blk i then t i else 1 with hr_def
  set a : κ → ℝ := fun j => ∑ w : InfinitePlace F, w (ξ j) with ha_def
  have ha0 : ∀ j, 0 ≤ a j := fun j => Finset.sum_nonneg fun w _ => apply_nonneg w _
  have hrt : ∀ i, ∀ j ∈ blk i, r j = t i := by
    intro i j hj
    simp only [hr_def]
    rw [Finset.prod_eq_single i]
    · rw [if_pos hj]
    · intro i' _ hi'
      rw [if_neg]
      exact fun hj' => Finset.disjoint_left.1 (hdis i' i hi') hj' hj
    · intro h; exact absurd (Finset.mem_univ i) h
  have hrm : ∀ j, m ≤ r j := by
    intro j
    by_cases h : ∃ i, j ∈ blk i
    · obtain ⟨i, hi⟩ := h
      rw [hrt i j hi]; exact (min_le_left c 1).trans (ht i)
    · push_neg at h
      have : r j = 1 := by
        simp only [hr_def]
        exact Finset.prod_eq_one fun i _ => if_neg (h i)
      rw [this]; exact min_le_right c 1
  have hr0 : ∀ j, 0 < r j := fun j => hm0.trans_le (hrm j)
  have hS : (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w
      (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) = 1 + ∑ j, r j * a j := by
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evI_blkScale, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedEmbedding.normAtPlace_smul, mixedEmbedding.normAtPlace_apply, abs_of_pos (hr0 j)]
  rw [hS]
  set S : ℝ := 1 + ∑ j, r j * a j with hS_def
  have hS1 : 1 ≤ S := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hr0 j).le (ha0 j))
  have hS0 : 0 < S := one_pos.trans_le hS1
  have hA : ∀ i, 1 + t i * ∑ j ∈ blk i, a j ≤ S := by
    intro i
    rw [hS_def, Finset.mul_sum]
    refine add_le_add le_rfl ?_
    calc ∑ j ∈ blk i, t i * a j = ∑ j ∈ blk i, r j * a j :=
          Finset.sum_congr rfl fun j hj => by rw [hrt i j hj]
      _ ≤ ∑ j, r j * a j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j _ _ => mul_nonneg (hr0 j).le (ha0 j)
  have hA0 : ∀ i, 0 ≤ 1 + t i * ∑ j ∈ blk i, a j := fun i =>
    add_nonneg zero_le_one (mul_nonneg (hc.le.trans (ht i)) (Finset.sum_nonneg fun j _ => ha0 j))
  have hB : m * (1 + ∑ j, a j) ≤ S := by
    rw [mul_add, mul_one, Finset.mul_sum, hS_def]
    exact add_le_add (min_le_right c 1) (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hrm j) (ha0 j))
  have hB0 : 0 < 1 + ∑ j, a j := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => ha0 j)
  have hP0 : 0 < (∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N := by
    refine mul_pos (Finset.prod_pos fun i _ => pow_pos ?_ N) (pow_pos hB0 N)
    exact one_pos.trans_le (le_add_of_nonneg_right (mul_nonneg (hc.le.trans (ht i))
      (Finset.sum_nonneg fun j _ => ha0 j)))
  have key : m ^ N * ((∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N) ≤ S ^ ((q + 1) * N) := by
    have h1 : ∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N ≤ S ^ (q * N) := by
      calc ∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N ≤ ∏ _i : Fin q, S ^ N :=
            Finset.prod_le_prod (fun i _ => pow_nonneg (hA0 i) N) fun i _ => pow_le_pow_left₀ (hA0 i) (hA i) N
        _ = S ^ (q * N) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    have h2 : (m * (1 + ∑ j, a j)) ^ N ≤ S ^ N := pow_le_pow_left₀ (mul_nonneg hm0.le hB0.le) hB N
    calc m ^ N * ((∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N)
        = (∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (m * (1 + ∑ j, a j)) ^ N := by rw [mul_pow]; ring
      _ ≤ S ^ (q * N) * S ^ N := mul_le_mul h1 h2 (pow_nonneg (mul_nonneg hm0.le hB0.le) N) (pow_nonneg hS0.le _)
      _ = S ^ ((q + 1) * N) := by rw [← pow_add]; ring_nf
  rw [← mul_inv]
  exact inv_anti₀ (mul_pos (pow_pos hm0 N) hP0) key

end GlobalTheory.ThKTorus.MajCompare
