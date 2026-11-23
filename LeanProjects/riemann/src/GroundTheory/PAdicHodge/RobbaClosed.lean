import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a b : ℤ → K} {ρ : ℝ}

def trunc (a : ℤ → K) (s : Set ℤ) : ℤ → K := s.indicator a

theorem norm_trunc_le (s : Set ℤ) (n : ℤ) : ‖trunc a s n‖ ≤ ‖a n‖ := by
  unfold trunc
  by_cases hn : n ∈ s <;> simp [hn]

theorem ConvergesAt.trunc (hρ : 0 < ρ) (h : ConvergesAt a ρ) (s : Set ℤ) :
    ConvergesAt (Laurent.trunc a s) ρ :=
  squeeze_zero (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (norm_trunc_le s n) (by positivity)) h

theorem gaussNorm_trunc_le (hρ : 0 < ρ) (h : ConvergesAt a ρ) (s : Set ℤ) :
    gaussNorm (trunc a s) ρ ≤ gaussNorm a ρ :=
  gaussNorm_le fun n => (mul_le_mul_of_nonneg_right (norm_trunc_le s n) (by positivity)).trans
    (h.le_gaussNorm n)

theorem weight_le_of_support_le {N : ℤ} (hsupp : ∀ n, N < n → a n = 0) {ρ' : ℝ} (hρ : 0 < ρ)
    (hle : ρ ≤ ρ') (n : ℤ) : ‖a n‖ * ρ' ^ n ≤ (‖a n‖ * ρ ^ n) * (ρ' / ρ) ^ N := by
  rcases le_or_gt n N with hn | hn
  · have hρ' : 0 < ρ' := hρ.trans_le hle
    have h1 : 1 ≤ ρ' / ρ := by rw [le_div_iff₀ hρ]; linarith
    have h2 : (ρ' / ρ) ^ n ≤ (ρ' / ρ) ^ N := zpow_le_zpow_right₀ h1 hn
    have e : ρ' ^ n = ρ ^ n * (ρ' / ρ) ^ n := by
      rw [div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ hρ.ne')]
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  · simp [hsupp n hn]

theorem ConvergesAt.of_support_le {N : ℤ} (hsupp : ∀ n, N < n → a n = 0) (h : ConvergesAt a ρ)
    (hρ : 0 < ρ) {ρ' : ℝ} (hle : ρ ≤ ρ') : ConvergesAt a ρ' := by
  have hρ' : 0 < ρ' := hρ.trans_le hle
  refine squeeze_zero (fun n => by positivity) (weight_le_of_support_le hsupp hρ hle) ?_
  simpa using h.mul_const ((ρ' / ρ) ^ N)

theorem gaussNorm_le_of_support_le {N : ℤ} (hsupp : ∀ n, N < n → a n = 0)
    (h : ConvergesAt a ρ) (hρ : 0 < ρ) {ρ' : ℝ} (hle : ρ ≤ ρ') :
    gaussNorm a ρ' ≤ gaussNorm a ρ * (ρ' / ρ) ^ N :=
  gaussNorm_le fun n => (weight_le_of_support_le hsupp hρ hle n).trans
    (mul_le_mul_of_nonneg_right (h.le_gaussNorm n) (by have := hρ.trans_le hle; positivity))

theorem weight_le_of_support_ge {N : ℤ} (hsupp : ∀ n, n < N → a n = 0) {ρ' : ℝ} (hρ' : 0 < ρ')
    (hle : ρ' ≤ ρ) (n : ℤ) : ‖a n‖ * ρ' ^ n ≤ (‖a n‖ * ρ ^ n) * (ρ' / ρ) ^ N := by
  rcases le_or_gt N n with hn | hn
  · have hρ : 0 < ρ := hρ'.trans_le hle
    have h0 : 0 < ρ' / ρ := div_pos hρ' hρ
    have h1 : ρ' / ρ ≤ 1 := by rw [div_le_one hρ]; exact hle
    have h2 : (ρ' / ρ) ^ n ≤ (ρ' / ρ) ^ N := zpow_le_zpow_right_of_le_one₀ h0 h1 hn
    have e : ρ' ^ n = ρ ^ n * (ρ' / ρ) ^ n := by
      rw [div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ hρ.ne')]
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  · simp [hsupp n hn]

theorem ConvergesAt.of_support_ge {N : ℤ} (hsupp : ∀ n, n < N → a n = 0) (h : ConvergesAt a ρ)
    {ρ' : ℝ} (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) : ConvergesAt a ρ' := by
  refine squeeze_zero (fun n => by positivity) (weight_le_of_support_ge hsupp hρ' hle) ?_
  simpa using h.mul_const ((ρ' / ρ) ^ N)

theorem gaussNorm_le_of_support_ge {N : ℤ} (hsupp : ∀ n, n < N → a n = 0)
    (h : ConvergesAt a ρ) {ρ' : ℝ} (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) :
    gaussNorm a ρ' ≤ gaussNorm a ρ * (ρ' / ρ) ^ N :=
  gaussNorm_le fun n => (weight_le_of_support_ge hsupp hρ' hle n).trans
    (mul_le_mul_of_nonneg_right (h.le_gaussNorm n) (by have := hρ'.trans_le hle; positivity))

theorem gaussNorm_zero (ρ : ℝ) : gaussNorm (0 : ℤ → K) ρ = 0 := by simp [gaussNorm]

theorem gaussNorm_eq_zero_iff (hρ : 0 < ρ) (h : ConvergesAt a ρ) : gaussNorm a ρ = 0 ↔ a = 0 := by
  constructor
  · intro h0; by_contra ha; exact (gaussNorm_pos hρ h ha).ne' h0
  · rintro rfl; exact gaussNorm_zero ρ

theorem gaussNorm_neg (a : ℤ → K) (ρ : ℝ) : gaussNorm (-a) ρ = gaussNorm a ρ := by
  simp [gaussNorm]

theorem gaussNorm_sub_comm (a b : ℤ → K) (ρ : ℝ) : gaussNorm (a - b) ρ = gaussNorm (b - a) ρ := by
  rw [← neg_sub, gaussNorm_neg]

theorem gaussNorm_add_le (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    gaussNorm (a + b) ρ ≤ max (gaussNorm a ρ) (gaussNorm b ρ) :=
  gaussNorm_le fun n => by
    simp only [Pi.add_apply]
    calc ‖a n + b n‖ * ρ ^ n ≤ max ‖a n‖ ‖b n‖ * ρ ^ n :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
      _ = max (‖a n‖ * ρ ^ n) (‖b n‖ * ρ ^ n) := max_mul_of_nonneg _ _ (by positivity)
      _ ≤ _ := max_le_max (ha.le_gaussNorm n) (hb.le_gaussNorm n)

theorem gaussNorm_sub_le (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    gaussNorm (a - b) ρ ≤ max (gaussNorm a ρ) (gaussNorm b ρ) := by
  rw [sub_eq_add_neg, ← gaussNorm_neg b]
  exact gaussNorm_add_le hρ ha hb.neg

end Laurent

namespace Laurent

variable {a b : ℤ → K} {ρ : ℝ}

section Limits

def limSeq (x : ℕ → ℤ → K) : ℤ → K := fun n => limUnder atTop fun k => x k n

def UCauchy (x : ℕ → ℤ → K) (ρ : ℝ) : Prop :=
  ∀ ε > 0, ∃ K₀, ∀ j ≥ K₀, ∀ n, ‖x (j + 1) n - x j n‖ * ρ ^ n ≤ ε

variable {x : ℕ → ℤ → K}

theorem UCauchy.tendsto (hρ : 0 < ρ) (h : UCauchy x ρ) (n : ℤ) :
    Tendsto (fun k => x k n) atTop (𝓝 (limSeq x n)) := by
  have hc : CauchySeq fun k => x k n := by
    refine NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_order.2 ⟨fun e he => Eventually.of_forall fun k => lt_of_lt_of_le he
      (norm_nonneg _), fun ε hε => ?_⟩
    have hρn : 0 < ρ ^ n := zpow_pos hρ n
    obtain ⟨K₀, hK⟩ := h (ε / 2 * ρ ^ n) (by positivity)
    filter_upwards [eventually_ge_atTop K₀] with j hj
    have := hK j hj n
    have : ‖x (j + 1) n - x j n‖ ≤ ε / 2 := le_of_mul_le_mul_right (by linarith) hρn
    linarith
  exact hc.tendsto_limUnder

theorem UCauchy.weight_sub_le (hρ : 0 < ρ) (h : UCauchy x ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀, ∀ k ≥ K₀, ∀ n, ‖limSeq x n - x k n‖ * ρ ^ n ≤ ε := by
  obtain ⟨K₀, hK⟩ := h ε hε
  refine ⟨K₀, fun k hk n => ?_⟩
  have hj : ∀ j, k ≤ j → ‖x j n - x k n‖ * ρ ^ n ≤ ε := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simp [hε.le]
    | succ j hkj ih =>
      have e : x (j + 1) n - x k n = (x (j + 1) n - x j n) + (x j n - x k n) := by ring
      rw [e]
      calc ‖(x (j + 1) n - x j n) + (x j n - x k n)‖ * ρ ^ n
          ≤ max ‖x (j + 1) n - x j n‖ ‖x j n - x k n‖ * ρ ^ n :=
            mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
        _ = max (‖x (j + 1) n - x j n‖ * ρ ^ n) (‖x j n - x k n‖ * ρ ^ n) :=
            max_mul_of_nonneg _ _ (by positivity)
        _ ≤ ε := max_le (hK j (hk.trans hkj) n) ih
  have hlim : Tendsto (fun j => ‖x j n - x k n‖ * ρ ^ n) atTop
      (𝓝 (‖limSeq x n - x k n‖ * ρ ^ n)) :=
    (((h.tendsto hρ n).sub_const (x k n)).norm).mul_const _
  exact le_of_tendsto hlim (eventually_ge_atTop k |>.mono hj)

theorem UCauchy.gaussNorm_sub_le (hρ : 0 < ρ) (h : UCauchy x ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀, ∀ k ≥ K₀, gaussNorm (limSeq x - x k) ρ ≤ ε := by
  obtain ⟨K₀, hK⟩ := h.weight_sub_le hρ hε
  exact ⟨K₀, fun k hk => gaussNorm_le fun n => hK k hk n⟩

theorem UCauchy.convergesAt (hρ : 0 < ρ) (h : UCauchy x ρ) (hx : ∀ k, ConvergesAt (x k) ρ) :
    ConvergesAt (limSeq x) ρ := by
  refine tendsto_order.2 ⟨fun e he => Eventually.of_forall fun n => lt_of_lt_of_le he
    (by positivity), fun ε hε => ?_⟩
  obtain ⟨K₀, hK⟩ := h.weight_sub_le hρ (half_pos hε)
  have hev := (hx K₀).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with n hn
  have e : limSeq x n = (limSeq x n - x K₀ n) + x K₀ n := by ring
  rw [e]
  calc ‖(limSeq x n - x K₀ n) + x K₀ n‖ * ρ ^ n
      ≤ max ‖limSeq x n - x K₀ n‖ ‖x K₀ n‖ * ρ ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
    _ = max (‖limSeq x n - x K₀ n‖ * ρ ^ n) (‖x K₀ n‖ * ρ ^ n) :=
        max_mul_of_nonneg _ _ (by positivity)
    _ < ε := max_lt ((hK K₀ le_rfl n).trans_lt (half_lt_self hε)) (hn.trans (half_lt_self hε))

theorem UCauchy.of_gaussNorm (hρ : 0 < ρ) (hconv : ∀ j, ConvergesAt (x (j + 1) - x j) ρ)
    (hδ : Tendsto (fun j => gaussNorm (x (j + 1) - x j) ρ) atTop (𝓝 0)) : UCauchy x ρ := by
  intro ε hε
  obtain ⟨K₀, hK⟩ := eventually_atTop.1 (hδ.eventually (gt_mem_nhds hε))
  exact ⟨K₀, fun j hj n => ((hconv j).le_gaussNorm n).trans (hK j hj).le⟩

end Limits

section Inverse

def domTail (a : ℤ → K) (N : ℤ) : ℤ → K := fun n => if n = 0 then 0 else a (n + N) / a N

def invDom (a : ℤ → K) (N : ℤ) : ℤ → K :=
  cmul (Pi.single (-N) (a N)⁻¹) (geomInv (domTail a N))

theorem eq_single_cmul_domTail {N : ℤ} (hN : a N ≠ 0) :
    a = cmul (Pi.single N (a N)) (Pi.single 0 1 + domTail a N) := by
  rw [cmul_single_left]
  funext n
  simp only [Pi.add_apply, domTail, Pi.single_apply]
  by_cases hn : n - N = 0
  · have : n = N := by omega
    subst this; simp
  · simp only [if_neg hn, zero_add, sub_add_cancel]
    field_simp

theorem domTail_spec (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) {N : ℤ}
    (hN : ∀ m, m ≠ N → ‖a m‖ * ρ ^ m < ‖a N‖ * ρ ^ N) :
    ConvergesAt (domTail a N) ρ ∧ gaussNorm (domTail a N) ρ < 1 := by
  have haN : a N ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Function.ne_iff.1 ha
    have := hN m (fun e => hm (e ▸ h0))
    rw [h0, norm_zero, zero_mul] at this
    exact absurd this (not_lt.2 (by positivity))
  have hW : 0 < ‖a N‖ * ρ ^ N := by have := norm_pos_iff.2 haN; positivity
  have hweight : ∀ n, n ≠ 0 → ‖domTail a N n‖ * ρ ^ n = ‖a (n + N)‖ * ρ ^ (n + N) / (‖a N‖ * ρ ^ N) := by
    intro n hn
    simp only [domTail, if_neg hn, norm_div]
    rw [zpow_add₀ hρ.ne']
    field_simp
  have hshift : Tendsto (fun n : ℤ => ‖a (n + N)‖ * ρ ^ (n + N) / (‖a N‖ * ρ ^ N)) cofinite
      (𝓝 0) := by
    have := (h.comp (add_left_injective N).tendsto_cofinite).div_const (‖a N‖ * ρ ^ N)
    simpa [Function.comp] using this
  have hconv : ConvergesAt (domTail a N) ρ := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hshift
    by_cases hn : n = 0
    · simp only [domTail, if_pos hn, norm_zero, zero_mul]; positivity
    · exact (hweight n hn).le
  refine ⟨hconv, ?_⟩
  by_cases hu0 : domTail a N = 0
  · rw [hu0, gaussNorm_zero]; exact one_pos
  obtain ⟨n, hn⟩ := hconv.exists_eq_gaussNorm hρ hu0
  rw [← hn]
  by_cases hn0 : n = 0
  · simp only [domTail, if_pos hn0, norm_zero, zero_mul]; exact one_pos
  · rw [hweight n hn0, div_lt_one hW]
    exact hN (n + N) (by omega)

theorem cmul_rearrange (hρ : 0 < ρ) {A B C W : ℤ → K} (hA : ConvergesAt A ρ)
    (hB : ConvergesAt B ρ) (hC : ConvergesAt C ρ) (hW : ConvergesAt W ρ) :
    cmul (cmul A B) (cmul C W) = cmul (cmul A C) (cmul B W) := by
  rw [cmul_assoc hρ hA hB (hC.cmul hρ hW), ← cmul_assoc hρ hB hC hW, cmul_comm B C,
    cmul_assoc hρ hC hB hW, ← cmul_assoc hρ hA hC (hB.cmul hρ hW)]

theorem invDom_spec (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) {N : ℤ}
    (hN : ∀ m, m ≠ N → ‖a m‖ * ρ ^ m < ‖a N‖ * ρ ^ N) :
    ConvergesAt (invDom a N) ρ ∧ cmul a (invDom a N) = Pi.single 0 1 := by
  have haN : a N ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Function.ne_iff.1 ha
    have := hN m (fun e => hm (e ▸ h0))
    rw [h0, norm_zero, zero_mul] at this
    exact absurd this (not_lt.2 (by positivity))
  obtain ⟨hu, hq⟩ := domTail_spec hρ h ha hN
  have hw := hu.geomInv hρ hq
  have hs1 := convergesAt_single N (a N) ρ
  have hs2 := convergesAt_single (-N) (a N)⁻¹ ρ
  refine ⟨hs2.cmul hρ hw, ?_⟩
  have e := eq_single_cmul_domTail haN
  rw [show cmul a (invDom a N) = cmul (cmul (Pi.single N (a N)) (Pi.single 0 1 + domTail a N))
    (invDom a N) from congrArg (fun x => cmul x (invDom a N)) e]
  unfold invDom
  rw [cmul_rearrange hρ hs1 ((convergesAt_single 0 1 ρ).add hρ hu) hs2 hw,
    cmul_one_add_geomInv hρ hu hq, cmul_single_zero_one, cmul_single_left]
  funext n
  simp only [Pi.single_apply, sub_neg_eq_add]
  by_cases hn : n = 0
  · subst hn; simp [haN]
  · simp [hn, show n + N ≠ N by omega]

theorem weight_lt_of_lowIndex_eq_highIndex (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
    (he : lowIndex a ρ = highIndex a ρ) (m : ℤ) (hm : m ≠ lowIndex a ρ) :
    ‖a m‖ * ρ ^ m < ‖a (lowIndex a ρ)‖ * ρ ^ (lowIndex a ρ) := by
  rw [show ‖a (lowIndex a ρ)‖ * ρ ^ (lowIndex a ρ) = gaussNorm a ρ from lowIndex_mem hρ h ha]
  rcases lt_or_gt_of_ne hm with hm | hm
  · exact weight_lt_of_lt_lowIndex hρ h ha hm
  · exact weight_lt_of_highIndex_lt hρ h ha (he ▸ hm)

end Inverse

end Laurent

namespace AnnulusRing

variable {I : Set ℝ} [Fact (∃ ρ ∈ I, 0 < ρ)]

instance : Nontrivial (AnnulusRing K I) :=
  ⟨⟨0, 1, fun h => by simpa using congrFun (congrArg AnnulusRing.coeff h) 0⟩⟩

instance : NoZeroDivisors (AnnulusRing K I) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    by_contra hfg
    push_neg at hfg
    have hf : f.coeff ≠ 0 := fun e => hfg.1 (AnnulusRing.ext e)
    have hg : g.coeff ≠ 0 := fun e => hfg.2 (AnnulusRing.ext e)
    exact cmul_ne_zero radius_pos f.conv g.conv hf hg (congrArg AnnulusRing.coeff h)

instance : IsDomain (AnnulusRing K I) := NoZeroDivisors.to_isDomain _

theorem isUnit_of_lowIndex_eq_highIndex {α β : ℝ} [Fact (∃ ρ ∈ Set.Icc α β, 0 < ρ)] (hα : 0 < α)
    (f : AnnulusRing K (Set.Icc α β)) (hf : f ≠ 0)
    (h : lowIndex f.coeff α = highIndex f.coeff β) : IsUnit f := by
  have hf0 : f.coeff ≠ 0 := fun e => hf (AnnulusRing.ext e)
  obtain ⟨ρ₀, hρ₀, -⟩ := (Fact.out : ∃ ρ ∈ Set.Icc α β, 0 < ρ)
  have hαβ : α ≤ β := hρ₀.1.trans hρ₀.2
  have hcα := f.convergesAt ⟨le_rfl, hαβ⟩ hα
  have hcβ := f.convergesAt ⟨hαβ, le_rfl⟩ (hα.trans_le hαβ)
  set N := lowIndex f.coeff α
  have key : ∀ ρ ∈ Set.Icc α β, lowIndex f.coeff ρ = N ∧ highIndex f.coeff ρ = N := by
    intro ρ hρ
    have hc := f.convergesAt hρ (hα.trans_le hρ.1)
    have h1 := lowIndex_mono hα hρ.1 hcα hc hf0
    have h2 := highIndex_mono (hα.trans_le hρ.1) hρ.2 hc hcβ hf0
    have h3 := lowIndex_le_highIndex (hα.trans_le hρ.1) hc hf0
    omega
  have hinv : ∀ ρ ∈ Set.Icc α β, ConvergesAt (invDom f.coeff N) ρ ∧
      cmul f.coeff (invDom f.coeff N) = Pi.single 0 1 := by
    intro ρ hρ
    have hρ0 := hα.trans_le hρ.1
    have hc := f.convergesAt hρ hρ0
    obtain ⟨k1, k2⟩ := key ρ hρ
    have := weight_lt_of_lowIndex_eq_highIndex hρ0 hc hf0 (k1.trans k2.symm)
    rw [k1] at this
    exact invDom_spec hρ0 hc hf0 this
  let g : AnnulusRing K (Set.Icc α β) :=
    ⟨invDom f.coeff N, fun ρ hρ _ => (hinv ρ hρ).1⟩
  have hfg : f * g = 1 := AnnulusRing.ext (hinv α ⟨le_rfl, hαβ⟩).2
  exact ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, rfl⟩

end AnnulusRing

namespace Robba

instance : NoZeroDivisors (Robba K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    by_contra hfg
    push_neg at hfg
    have hf : f.coeff ≠ 0 := fun e => hfg.1 (Robba.ext e)
    have hg : g.coeff ≠ 0 := fun e => hfg.2 (Robba.ext e)
    obtain ⟨r, hr0, hr1, hc⟩ := exists_common f g
    exact cmul_ne_zero hr0 (hc r le_rfl hr1).1 (hc r le_rfl hr1).2 hf hg
      (congrArg Robba.coeff h)

instance : IsDomain (Robba K) := NoZeroDivisors.to_isDomain _

end Robba

end GroundTheory.PAdicHodge
