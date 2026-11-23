import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FsInvPow

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_h_eq (a : K → ℤ) (z : (Σ k, ι k) → ℂ) :
    (fsHerm ι a).h z = (HermLine.ofMetrics (fun k => fsMetric (ι k)) a).h z := by
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h : (fsHerm ι a).h = (HermLine.ofMetrics (fun k => fsMetric (ι k)) a).h := funext (fsHerm_h_eq a)
  unfold IsSmoothHerm
  rw [h]
  exact Inter.isSmoothHerm_ofMetrics_fs a

theorem isSmoothHerm_fsMulti : IsSmoothHerm (GroundTheory.Heights₂.Heights.fsMulti ι) := by
  unfold GroundTheory.Heights₂.Heights.fsMulti
  exact Inter.isSmoothHerm_ofMetrics_fs _

abbrev invTensor (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  (fsHerm ι (fun _ => -1)).tensor (GroundTheory.Heights₂.Heights.fsMulti ι)

theorem isSmoothHerm_invTensor : IsSmoothHerm (invTensor ι) := by
  show ContDiffOn ℝ _ (fun z => (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z) _
  exact (isSmoothHerm_fsHerm _).mul isSmoothHerm_fsMulti

theorem invTensor_a (k : K) : (invTensor ι).a k = ((0 : K → ℕ) k : ℤ) := by
  show (-1 : ℤ) + 1 = _
  simp

theorem invTensor_h {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (invTensor ι).h z = 1 := by
  show (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z = 1
  rw [fsHerm_h_eq]
  unfold GroundTheory.Heights₂.Heights.fsMulti
  rw [Inter.ofMetrics_fs_h, Inter.ofMetrics_fs_h, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hS : Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩)).ne'
  show Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (-1 : ℤ) * Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (1 : ℤ) = 1
  rw [zpow_neg_one, zpow_one]
  exact inv_mul_cancel₀ hS

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_eq_zero {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
      · rfl
    simp [h0]
  · rfl

theorem snoc_invTensor (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    II K ι P (n + 1) (Fin.snoc L (invTensor ι)) = 0 := by
  have h1 : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
    classical
    intro m hm k
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  have hne : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [(hII K ι).2.2 P n L (invTensor ι) 1 0 hP hL isSmoothHerm_invTensor invTensor_a h1 hne]
  unfold recR
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    unfold divSupp
    rw [Ideal.span_singleton_one, sup_top_eq, Ideal.minimalPrimes_top]
    simp
  have hint : arInt P 1 (invTensor ι) L = 0 := by
    unfold arInt
    refine ptsIntegral_eq_zero P _ _ fun z hz => ?_
    simp [logNorm, invTensor_h hz.1]
  simp [hsupp, hint]

theorem intersection_update_fsHerm_neg_one (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (M : Fin (n + 1) → HermLine ι) (hP : IsArithVar P (n + 1)) (hM : ∀ i, IsSmoothHerm (M i))
    (j : Fin (n + 1)) :
    II K ι P (n + 1) (Function.update M j (fsHerm ι fun _ => -1)) =
      -II K ι P (n + 1) (Function.update M j (GroundTheory.Heights₂.Heights.fsMulti ι)) := by
  let σ := Equiv.swap j (Fin.last n)
  let L : Fin n → HermLine ι := fun i => M (σ (Fin.castSucc i))
  have hL : ∀ i, IsSmoothHerm (L i) := fun i => hM _
  have key : ∀ C, Function.update M j C ∘ σ = Fin.snoc L C := by
    intro C
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp only [Function.comp_apply, Fin.snoc_castSucc, L]
      rw [Function.update_of_ne]
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      exact (Fin.castSucc_lt_last i).ne h
  have hsm : ∀ C, IsSmoothHerm C → ∀ i, IsSmoothHerm (Function.update M j C i) := by
    intro C hC i
    by_cases h : i = j
    · subst h
      simpa using hC
    · rw [Function.update_of_ne h]
      exact hM i
  have hsym : ∀ C, IsSmoothHerm C →
      II K ι P (n + 1) (Function.update M j C) = II K ι P (n + 1) (Fin.snoc L C) := by
    intro C hC
    rw [← key C]
    exact ((hII K ι).1 P (n + 1) _ σ hP (hsm C hC)).symm
  rw [hsym _ (isSmoothHerm_fsHerm _), hsym _ isSmoothHerm_fsMulti]
  have hadd := (hII K ι).2.1 P n L (fsHerm ι fun _ => -1) (GroundTheory.Heights₂.Heights.fsMulti ι) hP hL
    (isSmoothHerm_fsHerm _) isSmoothHerm_fsMulti
  rw [snoc_invTensor II hII P n L hP hL] at hadd
  linarith

theorem proof : FsInvPow.Statement := by
  intro II K _ ι _ P d hII hP
  cases d with
  | zero =>
    rw [pow_zero, one_mul]
    congr 1
    funext i
    exact i.elim0
  | succ n =>
    let M : ℕ → Fin (n + 1) → HermLine ι := fun k i =>
      if (i : ℕ) < k then GroundTheory.Heights₂.Heights.fsMulti ι else fsHerm ι fun _ => -1
    have hM : ∀ k i, IsSmoothHerm (M k i) := by
      intro k i
      dsimp only [M]
      split_ifs
      · exact isSmoothHerm_fsMulti
      · exact isSmoothHerm_fsHerm _
    have step : ∀ k, (hk : k < n + 1) →
        II K ι P (n + 1) (M k) = -II K ι P (n + 1) (M (k + 1)) := by
      intro k hk
      have h1 : Function.update (M k) ⟨k, hk⟩ (fsHerm ι fun _ => -1) = M k := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
      have h2 : Function.update (M k) ⟨k, hk⟩ (GroundTheory.Heights₂.Heights.fsMulti ι) = M (k + 1) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
          have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          dsimp only [M]
          by_cases hi : (i : ℕ) < k
          · rw [if_pos hi, if_pos (by omega)]
          · rw [if_neg hi, if_neg (by omega)]
      rw [← h1, ← h2]
      exact intersection_update_fsHerm_neg_one II hII P n (M k) hP (hM k) ⟨k, hk⟩
    have hpow : ∀ k, k ≤ n + 1 → II K ι P (n + 1) (M 0) = (-1) ^ k * II K ι P (n + 1) (M k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [ih (by omega), step k (by omega), pow_succ]
        ring
    have h0 : M 0 = fun _ => fsHerm ι fun _ => -1 := by
      funext i
      simp [M]
    have hd : M (n + 1) = fun _ => GroundTheory.Heights₂.Heights.fsMulti ι := by
      funext i
      simp [M, i.isLt]
    rw [← h0, ← hd]
    exact hpow (n + 1) le_rfl

end FsInvPow

end GroundTheory.Heights₂.Heights.LowerBoundFree
