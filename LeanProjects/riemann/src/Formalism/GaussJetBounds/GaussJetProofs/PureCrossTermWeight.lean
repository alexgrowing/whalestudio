import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section SlopeTestRemainingChoices

variable {K : Type u} [NormedField K] {ι : Type v}

theorem wtGe_congr {pi : ℝ} {r : ι → ℝ} {wt wt' : ℝ} (h : wt = wt') {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) : WtGe pi r wt' f := by
  subst h
  exact hf

theorem wtGe_zero {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) (wt : ℝ) :
    WtGe pi r wt (0 : MvPowerSeries ι K) := by
  intro n
  unfold MonoWtGe
  rw [map_zero, norm_zero]
  exact Real.rpow_nonneg h0.le _

theorem dot_single (i : ι) (k : ℕ) (r : ι → ℝ) : dot (Finsupp.single i k) r = k * r i := by
  unfold dot
  rw [Finsupp.sum_single_index (by simp)]

theorem wtGe_CX {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) (i : ι) {c : K} (hc : ‖c‖ ≤ 1) :
    WtGe pi r (r i) (MvPowerSeries.C c * MvPowerSeries.X i) := by
  classical
  intro n
  unfold MonoWtGe
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs with h
  · subst h
    rw [mul_one, dot_single]
    simp only [Nat.cast_one, one_mul, sub_self, Real.rpow_zero]
    exact hc
  · rw [mul_zero, norm_zero]
    exact Real.rpow_nonneg h0.le _

theorem pow_pair_eq [DecidableEq ι] (i j : ι) (x y : K) (a b : ℕ) :
    (MvPowerSeries.C x * MvPowerSeries.X i) ^ a * (MvPowerSeries.C y * MvPowerSeries.X j) ^ b =
      MvPowerSeries.monomial (Finsupp.single i a + Finsupp.single j b) (x ^ a * y ^ b) := by
  rw [mul_pow, mul_pow, ← map_pow, ← map_pow, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq]
  rw [mul_mul_mul_comm, ← map_mul]
  first
    | (rw [MvPowerSeries.monomial_mul_monomial, one_mul, ← MvPowerSeries.monomial_zero_eq_C_apply,
        MvPowerSeries.monomial_mul_monomial, zero_add, mul_one])
    | (simp [MvPowerSeries.monomial_mul_monomial, ← MvPowerSeries.monomial_zero_eq_C_apply])

variable [IsUltrametricDist K]

theorem norm_natCast_le_of_dvd {l k : ℕ} (h : l ∣ k) : ‖(k : K)‖ ≤ ‖(l : K)‖ := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  first
    | exact IsUltrametricDist.norm_natCast_le_one K m
    | exact IsUltrametricDist.norm_natCast_le_one (R := K) m

theorem wtGe_mul_natCast {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) {k : ℕ} (hk : ‖(k : K)‖ ≤ pi) :
    WtGe pi r (wt + 1) (f * (k : MvPowerSeries ι K)) := by
  intro n
  have hfn := hf n
  unfold MonoWtGe at hfn ⊢
  first
    | rw [show (k : MvPowerSeries ι K) = MvPowerSeries.C (k : K) from (map_natCast _ k).symm,
        MvPowerSeries.coeff_mul_C, norm_mul]
    | rw [← map_natCast (MvPowerSeries.C (σ := ι) (R := K)) k, MvPowerSeries.coeff_mul_C, norm_mul]
  calc _ ≤ pi ^ (wt - dot n r) * pi := mul_le_mul hfn hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (wt + 1 - dot n r) := by
      rw [show wt + 1 - dot n r = (wt - dot n r) + 1 by ring, Real.rpow_add_one h0.ne']

theorem frob_two {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) {r : ι → ℝ} {wt : ℝ}
    {A B : MvPowerSeries ι K} (hA : WtGe ‖(l : K)‖ r wt A) (hB : WtGe ‖(l : K)‖ r wt B) :
    WtGe ‖(l : K)‖ r ((l : ℝ) * wt + 1) ((A + B) ^ l - A ^ l - B ^ l) := by
  obtain ⟨k, hk⟩ : ∃ k, l = k + 1 + 1 := ⟨l - 2, by have := hl.two_le; omega⟩
  have key : (A + B) ^ l - A ^ l - B ^ l = ∑ m ∈ Finset.range (k + 1),
      A ^ (m + 1) * B ^ (l - (m + 1)) * (l.choose (m + 1) : MvPowerSeries ι K) := by
    subst hk
    rw [add_pow, Finset.sum_range_succ _ (k + 1 + 1), Finset.sum_range_succ' _ (k + 1)]
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero,
      Nat.cast_one, mul_one, one_mul]
    abel
  rw [key]
  refine wtGe_sum hpi0 _ _ fun m hm => ?_
  have hm' : m + 1 < l := by rw [Finset.mem_range] at hm; omega
  have hdv : l ∣ l.choose (m + 1) := hl.dvd_choose_self (by omega) hm'
  refine wtGe_congr ?_ (wtGe_mul_natCast hpi0 (wtGe_mul hpi0 (wtGe_pow hpi0 hA (m + 1))
    (wtGe_pow hpi0 hB (l - (m + 1)))) (norm_natCast_le_of_dvd hdv))
  rw [Nat.cast_sub hm'.le]; push_cast; ring

theorem frob_sum {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) (hpi1 : ‖(l : K)‖ ≤ 1)
    {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α) (A : α → MvPowerSeries ι K)
    (hA : ∀ i ∈ s, WtGe ‖(l : K)‖ r wt (A i)) :
    WtGe ‖(l : K)‖ r ((l : ℝ) * wt + 1) ((∑ i ∈ s, A i) ^ l - ∑ i ∈ s, A i ^ l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow hl.ne_zero, sub_zero]
    exact wtGe_zero hpi0 r _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : WtGe ‖(l : K)‖ r wt (∑ i ∈ s, A i) :=
      wtGe_sum hpi0 s A fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have h1 := frob_two hl hpi0 (hA a (Finset.mem_insert_self a s)) hS
    have h2 := ih fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have h3 := wtGe_add hpi0 hpi1 h1 h2
    rw [min_self] at h3
    convert h3 using 1; ring

theorem frob_iter {l : ℕ} (hl : l.Prime) (hpi0 : 0 < ‖(l : K)‖) (hpi1 : ‖(l : K)‖ ≤ 1)
    {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α) (A : α → MvPowerSeries ι K)
    (hA : ∀ i ∈ s, WtGe ‖(l : K)‖ r wt (A i)) (k : ℕ) :
    WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt + 1)
      ((∑ i ∈ s, A i) ^ (l ^ k) - ∑ i ∈ s, A i ^ (l ^ k)) := by
  induction k with
  | zero =>
    simp only [pow_zero, pow_one, sub_self]
    exact wtGe_zero hpi0 r _
  | succ k ih =>
    set P := ∑ i ∈ s, A i ^ (l ^ k) with hP
    set E := (∑ i ∈ s, A i) ^ (l ^ k) - P with hE
    have hPw : WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt) P :=
      wtGe_sum hpi0 s _ fun i hi => wtGe_pow hpi0 (hA i hi) (l ^ k)
    have hEw' : WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt) E :=
      wtGe_mono hpi0 hpi1 (by linarith) ih
    have hPE : WtGe ‖(l : K)‖ r (((l ^ k : ℕ) : ℝ) * wt) (P + E) := by
      have := wtGe_add hpi0 hpi1 hPw hEw'; rwa [min_self] at this
    have hG : WtGe ‖(l : K)‖ r (((l - 1 : ℕ) : ℝ) * (((l ^ k : ℕ) : ℝ) * wt))
        (∑ i ∈ Finset.range l, (P + E) ^ i * P ^ (l - 1 - i)) := by
      refine wtGe_sum hpi0 _ _ fun i hi => ?_
      have hi' : i ≤ l - 1 := by rw [Finset.mem_range] at hi; omega
      refine wtGe_congr ?_ (wtGe_mul hpi0 (wtGe_pow hpi0 hPE i) (wtGe_pow hpi0 hPw (l - 1 - i)))
      rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hi']
    have h1 : WtGe ‖(l : K)‖ r (((l ^ (k + 1) : ℕ) : ℝ) * wt + 1) ((P + E) ^ l - P ^ l) := by
      rw [← geom_sum₂_mul, show P + E - P = E by abel]
      refine wtGe_congr ?_ (wtGe_mul hpi0 hG ih)
      have hl1 : 1 ≤ l := hl.one_lt.le
      rw [Nat.cast_sub hl1]; push_cast; ring
    have h2 : WtGe ‖(l : K)‖ r (((l ^ (k + 1) : ℕ) : ℝ) * wt + 1)
        (P ^ l - ∑ i ∈ s, A i ^ (l ^ (k + 1))) := by
      have := frob_sum hl hpi0 hpi1 s (fun i => A i ^ (l ^ k))
        fun i hi => wtGe_pow hpi0 (hA i hi) (l ^ k)
      simp only [← pow_mul, ← pow_succ] at this
      refine wtGe_congr ?_ this
      push_cast; ring
    have h3 := wtGe_add hpi0 hpi1 h1 h2
    rw [min_self] at h3
    have e : (∑ i ∈ s, A i) ^ l ^ (k + 1) = (P + E) ^ l := by
      rw [pow_succ, pow_mul, hE]; congr 1; abel
    rw [e]; convert h3 using 1; abel

end SlopeTestRemainingChoices

theorem pure_cross_term_weight : PureCross.{u, v} := by
  intro K _ _ _ l d N0 N1 _ hl hlt ι _ _ M hM be hbe0 hW hNB
  classical
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hlt.le
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff (linSub M x) = 0 := by
    intro x; simp [linSub]
  have hlinT : ∀ x i, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l)
      (MvPowerSeries.C (M x i) * MvPowerSeries.X i) :=
    fun x i => wtGe_CX h0 (fun _ => rho l) i (hM x i)
  have hlin : ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (linSub M x) := fun x =>
    wtGe_sum h0 Finset.univ _ fun i _ => hlinT x i
  have hsub : ∀ ab : Fin N0 × Fin N1,
      MvPowerSeries.HasSubst (fun s : ZMod d => linSub M (s, ab.1, ab.2)) :=
    fun ab => MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _
  have hp : ∀ (ab : Fin N0 × Fin N1) (n : ZMod d →₀ ℕ),
      WtGe ‖(l : K)‖ (fun _ : ι => rho l) (dot n (fun _ => rho l))
        (n.prod fun s e => linSub M (s, ab.1, ab.2) ^ e) := by
    intro ab n
    have := wtGe_prod h0 n.support (fun s => (n s : ℝ) * rho l)
      (fun s => linSub M (s, ab.1, ab.2) ^ n s) fun s _ => wtGe_pow h0 (hlin _) (n s)
    simpa [dot, Finsupp.sum, Finsupp.prod] using this
  refine ⟨?_, ?_⟩
  · unfold bSum
    refine wtGe_sum h0 _ _ fun ab _ => ?_
    exact substitution_weight_bound K ‖(l : K)‖ h0 hlt (ZMod d) ι _ (fun _ => rho l) (fun _ => rho l) _ be
      (fun s => hlin0 _) (fun s => hlin _) hW
  · intro m hm
    rw [monoWtGe_iff]
    unfold bSum
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun ab _ => ?_
    rw [MvPowerSeries.coeff_subst (hsub ab)]
    refine norm_finsum_le_of (Real.rpow_nonneg h0.le _) fun n => ?_
    rw [smul_eq_mul, norm_mul]
    by_cases hn : IsBiPower l n
    · obtain ⟨s, s', α, β, -, -, -, -, rfl⟩ := hn
      have hprod : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)).prod
          (fun t e => linSub M (t, ab.1, ab.2) ^ e) =
          linSub M (s, ab.1, ab.2) ^ (l ^ α) * linSub M (s', ab.1, ab.2) ^ (l ^ β) := by
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
      rw [hprod]
      set A := linSub M (s, ab.1, ab.2) with hA
      set B := linSub M (s', ab.1, ab.2) with hB
      set P := ∑ i, (MvPowerSeries.C (M (s, ab.1, ab.2) i) * MvPowerSeries.X i) ^ (l ^ α) with hP
      set P' := ∑ j, (MvPowerSeries.C (M (s', ab.1, ab.2) j) * MvPowerSeries.X j) ^ (l ^ β)
        with hP'
      have hEA : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ α : ℕ) : ℝ) * rho l + 1) (A ^ (l ^ α) - P) :=
        frob_iter hl h0 h1 Finset.univ _ (fun i _ => hlinT (s, ab.1, ab.2) i) α
      have hEB : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ β : ℕ) : ℝ) * rho l + 1) (B ^ (l ^ β) - P') :=
        frob_iter hl h0 h1 Finset.univ _ (fun i _ => hlinT (s', ab.1, ab.2) i) β
      have hPw : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ α : ℕ) : ℝ) * rho l) P :=
        wtGe_sum h0 _ _ fun i _ => wtGe_pow h0 (hlinT _ i) _
      have hBw : WtGe ‖(l : K)‖ (fun _ => rho l) (((l ^ β : ℕ) : ℝ) * rho l) (B ^ (l ^ β)) :=
        wtGe_pow h0 (hlin _) _
      have hD : WtGe ‖(l : K)‖ (fun _ => rho l)
          ((((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l) + 1)
          (A ^ (l ^ α) * B ^ (l ^ β) - P * P') := by
        have e : A ^ (l ^ α) * B ^ (l ^ β) - P * P' =
            (A ^ (l ^ α) - P) * B ^ (l ^ β) + P * (B ^ (l ^ β) - P') := by ring
        rw [e]
        have := wtGe_add h0 h1 (wtGe_mul h0 hEA hBw) (wtGe_mul h0 hPw hEB)
        refine wtGe_congr ?_ this
        rw [show ((l ^ α : ℕ) : ℝ) * rho l + 1 + ((l ^ β : ℕ) : ℝ) * rho l =
            ((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l + 1 by ring,
          show ((l ^ α : ℕ) : ℝ) * rho l + (((l ^ β : ℕ) : ℝ) * rho l + 1) =
            ((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l + 1 by ring, min_self]
      have hPP : MvPowerSeries.coeff m (P * P') = 0 := by
        rw [hP, hP', Finset.sum_mul_sum, map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [pow_pair_eq, MvPowerSeries.coeff_monomial_ne]
        exact fun h => hm ⟨i, j, α, β, h⟩
      have hcoef : MvPowerSeries.coeff m (A ^ (l ^ α) * B ^ (l ^ β)) =
          MvPowerSeries.coeff m (A ^ (l ^ α) * B ^ (l ^ β) - P * P') := by
        rw [map_sub, hPP, sub_zero]
      rw [hcoef]
      have hdn : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ => rho l) =
          ((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l := by
        rw [dot_add, dot_single, dot_single]
      have hbn := hW (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))
      rw [monoWtGe_iff, hdn] at hbn
      calc _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - 1 -
              (((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l)) *
            ‖(l : K)‖ ^ ((((l ^ α : ℕ) : ℝ) * rho l + ((l ^ β : ℕ) : ℝ) * rho l) + 1 -
              dot m (fun _ => rho l)) :=
          mul_le_mul hbn (hD m) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
        _ = _ := by rw [← Real.rpow_add h0]; congr 1; ring
    · have hb := hNB n hn
      rw [monoWtGe_iff] at hb
      calc _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n (fun _ => rho l)) *
            ‖(l : K)‖ ^ (dot n (fun _ => rho l) - dot m (fun _ => rho l)) :=
          mul_le_mul hb (hp ab n m) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
        _ = _ := by rw [← Real.rpow_add h0]; congr 1; ring

end Formalism.DworkPowerSeriesWeights
