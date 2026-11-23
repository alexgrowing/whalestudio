import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaUntilt
import GroundTheory.PAdicHodge.ExtRobbaComplete
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ξ : T.int} (hξ : T.IsPrimOne ξ)

instance instIsUltrametricDistUntiltField : IsUltrametricDist (T.UntiltField hξ) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (T.norm_untiltField_add_le hξ)

def ptPi : T.UntiltField hξ := T.toUntiltField hξ (T.toUntilt ξ T.πInt)

theorem norm_ptPi : ‖T.ptPi hξ‖ = ‖T.coeff (ξ : Γ) 0‖ := by
  rw [ptPi, norm_toUntiltField, T.untiltNorm_π hξ]

include hξ in
theorem ptRad_pos : 0 < ‖T.coeff (ξ : Γ) 0‖ := norm_pos_iff.2 hξ.coeff_zero_ne

include hξ in
theorem ptRad_lt_one : ‖T.coeff (ξ : Γ) 0‖ < 1 := hξ.norm_coeff_zero_lt

theorem ptPi_ne_zero : T.ptPi hξ ≠ 0 := by
  intro h
  have := T.norm_ptPi hξ
  rw [h, norm_zero] at this
  exact (T.ptRad_pos hξ).ne this

instance instNontriviallyNormedFieldUntiltField : NontriviallyNormedField (T.UntiltField hξ) where
  __ := (inferInstance : NormedField (T.UntiltField hξ))
  non_trivial := ⟨(T.ptPi hξ)⁻¹, by
    rw [norm_inv, T.norm_ptPi hξ]
    exact one_lt_inv_iff₀.2 ⟨T.ptRad_pos hξ, T.ptRad_lt_one hξ⟩⟩

def ptSharpInt {z : L} (hz : ‖z‖ ≤ 1) : T.UntiltField hξ :=
  T.toUntiltField hξ (T.toUntilt ξ (T.teichInt hz))

theorem norm_ptSharpInt {z : L} (hz : ‖z‖ ≤ 1) : ‖T.ptSharpInt hξ hz‖ = ‖z‖ := by
  rw [ptSharpInt, norm_toUntiltField, T.untiltNorm_teich hξ hz]

theorem ptSharpInt_mul {z w : L} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hzw : ‖z * w‖ ≤ 1) :
    T.ptSharpInt hξ hzw = T.ptSharpInt hξ hz * T.ptSharpInt hξ hw := by
  rw [ptSharpInt, ptSharpInt, ptSharpInt, T.toUntilt_teich_mul hz hw hzw, map_mul]

theorem ptSharpInt_congr {z w : L} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (h : z = w) :
    T.ptSharpInt hξ hz = T.ptSharpInt hξ hw := by subst h; rfl

theorem ptSharpInt_one : T.ptSharpInt hξ (show ‖(1 : L)‖ ≤ 1 by simp) = 1 := by
  rw [ptSharpInt]
  have : T.teichInt (show ‖(1 : L)‖ ≤ 1 by simp) = 1 := Subtype.ext (by simp [coe_teichInt, T.teich_one])
  rw [this, map_one, map_one]

open Classical in

def ptSharpFun (z : L) : T.UntiltField hξ :=
  if h : ‖z‖ ≤ 1 then T.ptSharpInt hξ h
  else (T.ptSharpInt hξ (show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_le.1 h).le))⁻¹

theorem ptSharpFun_of_le {z : L} (hz : ‖z‖ ≤ 1) : T.ptSharpFun hξ z = T.ptSharpInt hξ hz := by
  rw [ptSharpFun, dif_pos hz]

theorem ptSharpFun_of_gt {z : L} (hz : 1 < ‖z‖) :
    T.ptSharpFun hξ z = (T.ptSharpInt hξ (show ‖z⁻¹‖ ≤ 1 by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le))⁻¹ := by
  rw [ptSharpFun, dif_neg (not_le.2 hz)]

theorem norm_ptSharpFun (z : L) : ‖T.ptSharpFun hξ z‖ = ‖z‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [T.ptSharpFun_of_le hξ hz, norm_ptSharpInt]
  · rw [T.ptSharpFun_of_gt hξ (not_le.1 hz), norm_inv, norm_ptSharpInt, norm_inv, inv_inv]

theorem ptSharpFun_mul (z w : L) :
    T.ptSharpFun hξ (z * w) = T.ptSharpFun hξ z * T.ptSharpFun hξ w := by

  by_cases hz0 : z = 0
  · subst hz0
    have h0 : ∀ (h : ‖(0 : L)‖ ≤ 1), T.ptSharpInt hξ h = 0 := fun h => by
      rw [← norm_eq_zero, norm_ptSharpInt, norm_zero]
    rw [zero_mul, T.ptSharpFun_of_le hξ (by simp), h0, zero_mul]
  by_cases hw0 : w = 0
  · subst hw0
    have h0 : ∀ (h : ‖(0 : L)‖ ≤ 1), T.ptSharpInt hξ h = 0 := fun h => by
      rw [← norm_eq_zero, norm_ptSharpInt, norm_zero]
    rw [mul_zero, T.ptSharpFun_of_le hξ (by simp), h0, mul_zero]

  have key : ∀ {x : L} {a b : L} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hb0 : b ≠ 0), x * b = a →
      T.ptSharpFun hξ x * T.ptSharpInt hξ hb = T.ptSharpInt hξ ha := by
    intro x a b ha hb hb0 hxab
    by_cases hx : ‖x‖ ≤ 1
    · rw [T.ptSharpFun_of_le hξ hx, ← T.ptSharpInt_mul hξ hx hb (by rw [hxab]; exact ha)]
      exact T.ptSharpInt_congr hξ _ _ hxab
    · have hx1 : 1 < ‖x‖ := not_le.1 hx
      have hx0 : x ≠ 0 := by rintro rfl; exact absurd hx1 (by simp)
      have hxi : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx1.le
      rw [T.ptSharpFun_of_gt hξ hx1]

      have hb' : b = x⁻¹ * a := by rw [← hxab]; field_simp
      have hne : T.ptSharpInt hξ hxi ≠ 0 := by
        intro h0
        have := T.norm_ptSharpInt hξ hxi
        rw [h0, norm_zero, norm_inv] at this
        exact (inv_pos.2 (zero_lt_one.trans hx1)).ne this
      rw [T.ptSharpInt_congr hξ hb (by rw [← hb']; exact hb) hb', T.ptSharpInt_mul hξ hxi ha
        (by rw [← hb']; exact hb)]
      exact inv_mul_cancel_left₀ hne _

  have rep : ∀ x : L, x ≠ 0 → ∃ a b : L, ∃ (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1), b ≠ 0 ∧ x * b = a := by
    intro x hx
    by_cases h : ‖x‖ ≤ 1
    · exact ⟨x, 1, h, by simp, one_ne_zero, mul_one x⟩
    · refine ⟨1, x⁻¹, by simp, by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_le.1 h).le,
        inv_ne_zero hx, mul_inv_cancel₀ hx⟩
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := rep z hz0
  obtain ⟨c, d, hc, hd, hd0, hcd⟩ := rep w hw0
  have hbd : ‖b * d‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ hb (norm_nonneg _) hd
  have hac : ‖a * c‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hc
  have h1 := key hac hbd (mul_ne_zero hb0 hd0) (show z * w * (b * d) = a * c by
    rw [← hab, ← hcd]; ring)
  have h2 := key ha hb hb0 hab
  have h3 := key hc hd hd0 hcd
  have hbd0 : T.ptSharpInt hξ hbd ≠ 0 := by
    intro h0; have := T.norm_ptSharpInt hξ hbd
    rw [h0, norm_zero] at this; exact (mul_ne_zero hb0 hd0) (norm_eq_zero.1 this.symm)
  rw [T.ptSharpInt_mul hξ hb hd hbd, T.ptSharpInt_mul hξ ha hc hac] at h1
  rw [← h2, ← h3] at h1
  have hprod : T.ptSharpInt hξ hb * T.ptSharpInt hξ hd ≠ 0 := by
    rwa [← T.ptSharpInt_mul hξ hb hd hbd]
  exact mul_right_cancel₀ hprod (by rw [h1]; ring)

def ptSharp : L →*₀ T.UntiltField hξ where
  toFun := T.ptSharpFun hξ
  map_zero' := by
    rw [T.ptSharpFun_of_le hξ (by simp), ← norm_eq_zero, norm_ptSharpInt, norm_zero]
  map_one' := by rw [T.ptSharpFun_of_le hξ (by simp), ptSharpInt_one]
  map_mul' := T.ptSharpFun_mul hξ

theorem norm_ptSharp (z : L) : ‖T.ptSharp hξ z‖ = ‖z‖ := T.norm_ptSharpFun hξ z

theorem ptSharp_of_le {z : L} (hz : ‖z‖ ≤ 1) : T.ptSharp hξ z = T.ptSharpInt hξ hz :=
  T.ptSharpFun_of_le hξ hz

def ptRad (ξ : T.int) : ℝ := ‖T.coeff (ξ : Γ) 0‖

include hξ in
theorem ptRad_pos' : 0 < T.ptRad ξ := T.ptRad_pos hξ

include hξ in
theorem ptRad_lt_one' : T.ptRad ξ < 1 := T.ptRad_lt_one hξ

def ptTerm (a : ℤ → L) (n : ℤ) : T.UntiltField hξ := T.ptPi hξ ^ n * T.ptSharp hξ (a n)

theorem norm_ptTerm (a : ℤ → L) (n : ℤ) : ‖T.ptTerm hξ a n‖ = ‖a n‖ * T.ptRad ξ ^ n := by
  rw [ptTerm, norm_mul, norm_zpow, norm_ptPi, norm_ptSharp, mul_comm]; rfl

theorem tendsto_ptTerm {a : ℤ → L} (ha : ConvergesAt a (T.ptRad ξ)) :
    Tendsto (T.ptTerm hξ a) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_ptTerm]
  exact ha

theorem summable_ptTerm {a : ℤ → L} (ha : ConvergesAt a (T.ptRad ξ)) :
    Summable (T.ptTerm hξ a) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (T.tendsto_ptTerm hξ ha)

def ptEvalSeq (a : ℤ → L) : T.UntiltField hξ := ∑' n, T.ptTerm hξ a n

theorem norm_ptEvalSeq_le {a : ℤ → L} (ha : ConvergesAt a (T.ptRad ξ)) :
    ‖T.ptEvalSeq hξ a‖ ≤ gaussNorm a (T.ptRad ξ) :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gaussNorm_nonneg (T.ptRad_pos' hξ))
    fun n => by rw [norm_ptTerm]; exact ha.le_gaussNorm n

theorem ptEvalSeq_smul (d : L) (a : ℤ → L) (ha : ConvergesAt a (T.ptRad ξ)) :
    T.ptEvalSeq hξ (fun n => d * a n) = T.ptSharp hξ d * T.ptEvalSeq hξ a := by
  rw [ptEvalSeq, ptEvalSeq, ← (T.summable_ptTerm hξ ha).tsum_mul_left]
  congr 1
  funext n
  simp only [ptTerm, map_mul]
  ring

theorem ptEvalSeq_shift (a : ℤ → L) (N : ℤ) :
    T.ptEvalSeq hξ (fun k => a (k + N)) = T.ptPi hξ ^ (-N) * T.ptEvalSeq hξ a := by
  by_cases ha : Summable (T.ptTerm hξ a)
  · rw [ptEvalSeq, ptEvalSeq, ← ha.tsum_mul_left]
    have e : (fun k => T.ptTerm hξ (fun k => a (k + N)) k) =
        (fun j => T.ptPi hξ ^ (-N) * T.ptTerm hξ a j) ∘ (Equiv.addRight N) := by
      funext k
      simp only [Function.comp, Equiv.coe_addRight, ptTerm]
      rw [← mul_assoc, ← zpow_add₀ (T.ptPi_ne_zero hξ)]
      congr 2; ring
    rw [e]
    exact (Equiv.addRight N).tsum_eq (fun j => T.ptPi hξ ^ (-N) * T.ptTerm hξ a j)
  · have hb : ¬ Summable (T.ptTerm hξ (fun k => a (k + N))) := by
      intro hs
      apply ha
      have e : T.ptTerm hξ a = (fun k => T.ptPi hξ ^ N * T.ptTerm hξ (fun k => a (k + N)) k) ∘
          (Equiv.addRight N).symm := by
        funext j
        simp only [Function.comp, Equiv.coe_addRight, Equiv.addRight_symm, ptTerm, sub_add_cancel]
        rw [← mul_assoc, ← zpow_add₀ (T.ptPi_ne_zero hξ)]
        congr 2 <;> ring_nf
      rw [e]
      exact ((Equiv.addRight N).symm.summable_iff).2 (hs.mul_left _)
    rw [ptEvalSeq, ptEvalSeq, tsum_eq_zero_of_not_summable hb, tsum_eq_zero_of_not_summable ha,
      mul_zero]

def ptE (X : Γ) : T.UntiltField hξ := T.ptEvalSeq hξ (T.zcoeff X)

theorem ptE_finSum (a : ℕ → L) (N : ℕ) :
    T.ptE hξ (T.finSum a N) = ∑ n ∈ Finset.range N, T.ptPi hξ ^ (n : ℤ) * T.ptSharp hξ (a n) := by
  classical
  rw [ptE, ptEvalSeq, tsum_eq_sum (s := (Finset.range N).map Nat.castEmbedding)]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [ptTerm, Nat.castEmbedding_apply, zcoeff_natCast, coeff_finSum,
      if_pos (Finset.mem_range.1 hn)]
  · intro k hk
    simp only [ptTerm]
    rcases lt_or_ge k 0 with hk0 | hk0
    · rw [T.zcoeff_of_neg _ hk0, map_zero, mul_zero]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
      rw [zcoeff_natCast, coeff_finSum, if_neg, map_zero, mul_zero]
      intro hn
      exact hk (Finset.mem_map.2 ⟨n, Finset.mem_range.2 hn, rfl⟩)

theorem ptE_teich_mul (d : L) (X : Γ) (hX : ConvergesAt (T.zcoeff X) (T.ptRad ξ)) :
    T.ptE hξ (T.teich d * X) = T.ptSharp hξ d * T.ptE hξ X := by
  rw [ptE, ptE, ← T.ptEvalSeq_smul hξ d _ hX]
  congr 1
  funext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, T.zcoeff_of_neg _ hn, mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zcoeff_natCast, zcoeff_natCast, coeff_teich_mul]

theorem toUntilt_finSum {a : ℕ → L} {N : ℕ} (ha : ∀ i, ‖a i‖ ≤ 1) :
    T.toUntiltField hξ (T.toUntilt ξ ⟨T.finSum a N, T.finSum_mem_int fun i _ => ha i⟩) =
      ∑ n ∈ Finset.range N, T.ptPi hξ ^ (n : ℤ) * T.ptSharp hξ (a n) := by
  have e : (⟨T.finSum a N, T.finSum_mem_int fun i _ => ha i⟩ : T.int) =
      ∑ n ∈ Finset.range N, T.πInt ^ n * T.teichInt (ha n) := by
    apply Subtype.ext
    simp only [finSum, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, SubmonoidClass.coe_pow,
      coe_πInt, coe_teichInt]
  rw [e, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, T.ptSharp_of_le hξ (ha n), zpow_natCast]
  rfl

theorem zcoeff_sub_partialSum (X : Γ) (N : ℕ) (n : ℤ) :
    T.zcoeff (X - T.partialSum X N) n = if (N : ℤ) ≤ n then T.zcoeff X n else 0 := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zcoeff_natCast, zcoeff_natCast, coeff_sub_partialSum]
    by_cases h : m < N
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]

theorem zcoeff_partialSum (X : Γ) (N : ℕ) (n : ℤ) :
    T.zcoeff (T.partialSum X N) n = T.zcoeff X n - T.zcoeff (X - T.partialSum X N) n := by
  rw [zcoeff_sub_partialSum]
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, T.zcoeff_of_neg _ hn, if_neg (by omega), sub_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zcoeff_natCast, zcoeff_natCast, partialSum, coeff_finSum]
    by_cases h : m < N
    · rw [if_pos h, if_neg (by omega), sub_zero]
    · rw [if_neg h, if_pos (by omega), sub_self]

theorem convergesAt_sub_partialSum {X : Γ} {ρ : ℝ} (hρ : 0 < ρ) (hX : ConvergesAt (T.zcoeff X) ρ)
    (N : ℕ) : ConvergesAt (T.zcoeff (X - T.partialSum X N)) ρ := by
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hX
  rw [zcoeff_sub_partialSum]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_mul]; positivity

theorem zcoeff_partialSum' (X : Γ) (N : ℕ) (n : ℤ) :
    T.zcoeff (T.partialSum X N) n = if (N : ℤ) ≤ n then 0 else T.zcoeff X n := by
  rw [zcoeff_partialSum, zcoeff_sub_partialSum]
  split_ifs <;> simp

theorem convergesAt_partialSum' {X : Γ} {ρ : ℝ} (hρ : 0 < ρ) (hX : ConvergesAt (T.zcoeff X) ρ)
    (N : ℕ) : ConvergesAt (T.zcoeff (T.partialSum X N)) ρ := by
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hX
  rw [zcoeff_partialSum']
  split_ifs
  · rw [norm_zero, zero_mul]; positivity
  · exact le_rfl

theorem tendsto_gaussNorm_sub_partialSum {X : Γ} {ρ : ℝ} (hρ : 0 < ρ)
    (hX : ConvergesAt (T.zcoeff X) ρ) :
    Tendsto (fun N : ℕ => gaussNorm (T.zcoeff (X - T.partialSum X N)) ρ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB⟩ := (hX.finite_le (half_pos hε)).bddAbove
  refine ⟨(max B 0).toNat + 1, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (gaussNorm_nonneg hρ)]
  refine lt_of_le_of_lt (gaussNorm_le fun n => ?_) (half_lt_self hε)
  rw [zcoeff_sub_partialSum]
  split_ifs with h
  · refine le_of_lt (not_le.1 fun hc => ?_)
    have := hB (show n ∈ {n | ε / 2 ≤ ‖T.zcoeff X n‖ * ρ ^ n} from hc)
    have h2 : (((max B 0).toNat : ℕ) : ℤ) ≥ max B 0 := Int.self_le_toNat _
    omega
  · simp only [norm_zero, zero_mul]; linarith

theorem ptE_sub_partialSum {X : Γ} (hX : ConvergesAt (T.zcoeff X) (T.ptRad ξ)) (N : ℕ) :
    T.ptE hξ X - T.ptE hξ (T.partialSum X N) = T.ptEvalSeq hξ (T.zcoeff (X - T.partialSum X N)) := by
  rw [ptE, ptE, ptEvalSeq, ptEvalSeq, ← (T.summable_ptTerm hξ hX).tsum_sub
    (T.summable_ptTerm hξ (T.convergesAt_partialSum' (T.ptRad_pos' hξ) hX N))]
  congr 1
  funext n
  simp only [ptTerm, T.zcoeff_partialSum' X N n, T.zcoeff_sub_partialSum X N n]
  split_ifs <;> simp

theorem tendsto_ptE_partialSum {X : Γ} (hX : ConvergesAt (T.zcoeff X) (T.ptRad ξ)) :
    Tendsto (fun N : ℕ => T.ptE hξ (T.partialSum X N)) atTop (𝓝 (T.ptE hξ X)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    (T.tendsto_gaussNorm_sub_partialSum (T.ptRad_pos' hξ) hX)
  rw [norm_sub_rev, T.ptE_sub_partialSum hξ hX N]
  exact T.norm_ptEvalSeq_le hξ (T.convergesAt_sub_partialSum (T.ptRad_pos' hξ) hX N)

theorem norm_ptE_le {X : Γ} (hX : ConvergesAt (T.zcoeff X) (T.ptRad ξ)) :
    ‖T.ptE hξ X‖ ≤ gaussNorm (T.zcoeff X) (T.ptRad ξ) := T.norm_ptEvalSeq_le hξ hX

theorem ptE_int {X : Γ} (hX : X ∈ T.int) :
    T.ptE hξ X = T.toUntiltField hξ (T.toUntilt ξ ⟨X, hX⟩) := by
  have hXc : ConvergesAt (T.zcoeff X) (T.ptRad ξ) :=
    T.convergesAt_of_mem_int hX (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ)
  have hcoef : ∀ i, ‖T.coeff X i‖ ≤ 1 := T.mem_int_iff.1 hX
  have hmem : ∀ N, T.partialSum X N ∈ T.int := fun N => T.finSum_mem_int fun i _ => hcoef i

  have hval : ∀ N, T.ptE hξ (T.partialSum X N) =
      T.toUntiltField hξ (T.toUntilt ξ ⟨T.partialSum X N, hmem N⟩) := fun N => by
    exact (T.ptE_finSum hξ (T.coeff X) N).trans (T.toUntilt_finSum hξ hcoef).symm
  refine tendsto_nhds_unique (T.tendsto_ptE_partialSum hξ hXc) ?_
  simp_rw [hval]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (T.ptRad_pos' hξ).le (T.ptRad_lt_one' hξ)))

  have hZ := T.exists_int_of_eq_π_pow_mul (sub_mem hX (hmem N)) (T.sub_partialSum X N)
  have hXZ := T.sub_partialSum X N
  have hsub : (⟨T.partialSum X N, hmem N⟩ : T.int) - ⟨X, hX⟩ =
      -(T.πInt ^ N * ⟨T.tail^[N] X, hZ⟩) := by
    apply Subtype.ext
    push_cast
    simp only [coe_πInt]
    linear_combination -hXZ
  rw [← map_sub, ← map_sub, hsub, map_neg, map_neg, norm_neg, map_mul, map_mul, norm_mul,
    map_pow, map_pow, norm_pow, norm_toUntiltField, T.untiltNorm_π hξ, norm_toUntiltField]
  calc ‖T.coeff (ξ : Γ) 0‖ ^ N * T.untiltNorm hξ (T.toUntilt ξ ⟨T.tail^[N] X, hZ⟩)
      ≤ ‖T.coeff (ξ : Γ) 0‖ ^ N * 1 :=
        mul_le_mul_of_nonneg_left (T.untiltNorm_le_one hξ _) (pow_nonneg (norm_nonneg _) _)
    _ = T.ptRad ξ ^ N := by rw [mul_one]; rfl

def IsBddElt (U : Γ) : Prop := ∃ d : L, d ≠ 0 ∧ ‖d‖ ≤ 1 ∧ T.teich d * U ∈ T.int

theorem isBddElt_of_le {U : Γ} {M : ℝ} (h : ∀ n, ‖T.coeff U n‖ ≤ M) : T.IsBddElt U := by
  obtain ⟨d, hd0, hd⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < min 1 (1 / (|M| + 1)) by
    positivity)
  refine ⟨d, norm_pos_iff.1 hd0, (hd.trans_le (min_le_left _ _)).le, T.mem_int_iff.2 fun n => ?_⟩
  rw [coeff_teich_mul, norm_mul]
  have h1 : ‖d‖ ≤ 1 / (|M| + 1) := (hd.trans_le (min_le_right _ _)).le
  calc ‖d‖ * ‖T.coeff U n‖ ≤ (1 / (|M| + 1)) * (|M| + 1) :=
        mul_le_mul h1 ((h n).trans ((le_abs_self M).trans (by linarith))) (norm_nonneg _)
          (by positivity)
    _ = 1 := by field_simp

theorem isBddElt_partialSum (X : Γ) (N : ℕ) : T.IsBddElt (T.partialSum X N) := by
  refine T.isBddElt_of_le (M := ∑ i ∈ Finset.range N, ‖T.coeff X i‖) fun n => ?_
  rw [show T.partialSum X N = T.finSum (T.coeff X) N from rfl, coeff_finSum]
  split_ifs with h
  · exact Finset.single_le_sum (f := fun i => ‖T.coeff X i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.2 h)
  · rw [norm_zero]; exact Finset.sum_nonneg fun i _ => norm_nonneg _

theorem IsBddElt.common {U V : Γ} (hU : T.IsBddElt U) (hV : T.IsBddElt V) :
    ∃ d : L, d ≠ 0 ∧ ‖d‖ ≤ 1 ∧ T.teich d * U ∈ T.int ∧ T.teich d * V ∈ T.int := by
  obtain ⟨d, hd0, hd1, hdU⟩ := hU
  obtain ⟨e, he0, he1, heV⟩ := hV
  refine ⟨d * e, mul_ne_zero hd0 he0, by rw [norm_mul]; exact mul_le_one₀ hd1 (norm_nonneg _) he1,
    ?_, ?_⟩
  · have : T.teich (d * e) * U = T.teich e * (T.teich d * U) := by rw [T.teich_mul]; ring
    rw [this]
    exact T.int.mul_mem (T.teich_mem_int he1) hdU
  · rw [T.teich_mul, mul_assoc]
    exact T.int.mul_mem (T.teich_mem_int hd1) heV

theorem IsBddElt.add {U V : Γ} (hU : T.IsBddElt U) (hV : T.IsBddElt V) : T.IsBddElt (U + V) := by
  obtain ⟨d, hd0, hd1, hdU, hdV⟩ := hU.common T hV
  exact ⟨d, hd0, hd1, by rw [mul_add]; exact T.int.add_mem hdU hdV⟩

theorem IsBddElt.neg {U : Γ} (hU : T.IsBddElt U) : T.IsBddElt (-U) := by
  obtain ⟨d, hd0, hd1, hdU⟩ := hU
  exact ⟨d, hd0, hd1, by rw [mul_neg]; exact T.int.neg_mem hdU⟩

theorem IsBddElt.sub {U V : Γ} (hU : T.IsBddElt U) (hV : T.IsBddElt V) : T.IsBddElt (U - V) := by
  rw [sub_eq_add_neg]; exact hU.add T hV.neg

theorem IsBddElt.mul {U V : Γ} (hU : T.IsBddElt U) (hV : T.IsBddElt V) : T.IsBddElt (U * V) := by
  obtain ⟨d, hd0, hd1, hdU⟩ := hU
  obtain ⟨e, he0, he1, heV⟩ := hV
  refine ⟨d * e, mul_ne_zero hd0 he0, by rw [norm_mul]; exact mul_le_one₀ hd1 (norm_nonneg _) he1,
    ?_⟩
  rw [T.teich_mul, show T.teich d * T.teich e * (U * V) = (T.teich d * U) * (T.teich e * V) by ring]
  exact T.int.mul_mem hdU heV

theorem convergesAt_of_isBddElt {U : Γ} (hU : T.IsBddElt U) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.zcoeff U) ρ := by
  obtain ⟨d, hd0, hd1, hdU⟩ := hU
  have h := T.convergesAt_of_mem_int hdU hρ0 hρ1
  have e : T.zcoeff U = fun n => d⁻¹ * T.zcoeff (T.teich d * U) n := by
    funext n
    rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, T.zcoeff_of_neg _ hn, mul_zero]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [zcoeff_natCast, zcoeff_natCast, coeff_teich_mul, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
  rw [e]
  have := h.const_mul (‖d⁻¹‖)
  simp only [mul_zero] at this
  refine this.congr fun n => ?_
  rw [norm_mul]; ring

theorem sharp_ne_zero {d : L} (hd : d ≠ 0) : T.ptSharp hξ d ≠ 0 := by
  intro h
  have := T.norm_ptSharp hξ d
  rw [h, norm_zero] at this
  exact hd (norm_eq_zero.1 this.symm)

theorem ptE_add_of_bdd {U V : Γ} (hU : T.IsBddElt U) (hV : T.IsBddElt V) :
    T.ptE hξ (U + V) = T.ptE hξ U + T.ptE hξ V := by
  obtain ⟨d, hd0, hd1, hdU, hdV⟩ := hU.common T hV
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hUc := T.convergesAt_of_isBddElt hU hr0 hr1
  have hVc := T.convergesAt_of_isBddElt hV hr0 hr1
  have hUVc := T.convergesAt_of_isBddElt (hU.add T hV) hr0 hr1
  have h1 := T.ptE_teich_mul hξ d (U + V) hUVc
  have h2 : T.teich d * (U + V) ∈ T.int := by rw [mul_add]; exact T.int.add_mem hdU hdV
  rw [T.ptE_int hξ h2] at h1
  have e : (⟨T.teich d * (U + V), h2⟩ : T.int) = ⟨T.teich d * U, hdU⟩ + ⟨T.teich d * V, hdV⟩ :=
    Subtype.ext (by push_cast; ring)
  rw [e, map_add, map_add, ← T.ptE_int hξ hdU, ← T.ptE_int hξ hdV, T.ptE_teich_mul hξ d U hUc,
    T.ptE_teich_mul hξ d V hVc, ← mul_add] at h1
  exact (mul_left_cancel₀ (T.sharp_ne_zero hξ hd0) h1).symm

theorem ptE_mul_of_bdd {U V : Γ} (hU : T.IsBddElt U) (hV : T.IsBddElt V) :
    T.ptE hξ (U * V) = T.ptE hξ U * T.ptE hξ V := by
  obtain ⟨d, hd0, hd1, hdU, hdV⟩ := hU.common T hV
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hUc := T.convergesAt_of_isBddElt hU hr0 hr1
  have hVc := T.convergesAt_of_isBddElt hV hr0 hr1
  have hUVc := T.convergesAt_of_isBddElt (hU.mul T hV) hr0 hr1
  have h2 : T.teich (d * d) * (U * V) ∈ T.int := by
    rw [T.teich_mul, show T.teich d * T.teich d * (U * V) = (T.teich d * U) * (T.teich d * V) by ring]
    exact T.int.mul_mem hdU hdV
  have hA := T.ptE_teich_mul hξ (d * d) (U * V) hUVc
  have h1 := T.ptE_int hξ h2
  have e : (⟨T.teich (d * d) * (U * V), h2⟩ : T.int) =
      ⟨T.teich d * U, hdU⟩ * ⟨T.teich d * V, hdV⟩ :=
    Subtype.ext (by push_cast; rw [T.teich_mul]; ring)
  rw [hA, e, map_mul (T.toUntilt ξ), map_mul (T.toUntiltField hξ), ← T.ptE_int hξ hdU,
    ← T.ptE_int hξ hdV, T.ptE_teich_mul hξ d U hUc, T.ptE_teich_mul hξ d V hVc,
    map_mul (T.ptSharp hξ)] at h1
  have hs := T.sharp_ne_zero hξ hd0
  have : T.ptSharp hξ d * T.ptSharp hξ d * T.ptE hξ (U * V) =
      T.ptSharp hξ d * T.ptSharp hξ d * (T.ptE hξ U * T.ptE hξ V) := by
    rw [h1]; ring
  exact mul_left_cancel₀ (mul_ne_zero hs hs) this

theorem ptE_one : T.ptE hξ 1 = 1 := by
  rw [T.ptE_int hξ T.int.one_mem]
  rw [show (⟨1, T.int.one_mem⟩ : T.int) = 1 from rfl, map_one, map_one]

theorem ptE_zero : T.ptE hξ 0 = 0 := by
  rw [T.ptE_int hξ T.int.zero_mem]
  rw [show (⟨0, T.int.zero_mem⟩ : T.int) = 0 from rfl, map_zero, map_zero]

theorem gaussNorm_partialSum_le {X : Γ} {ρ : ℝ} (hρ : 0 < ρ) (hX : ConvergesAt (T.zcoeff X) ρ)
    (N : ℕ) : gaussNorm (T.zcoeff (T.partialSum X N)) ρ ≤ gaussNorm (T.zcoeff X) ρ := by
  refine gaussNorm_le fun n => ?_
  rw [zcoeff_partialSum']
  split_ifs
  · rw [norm_zero, zero_mul]; exact gaussNorm_nonneg hρ
  · exact hX.le_gaussNorm n

theorem ptE_add {X Y : Γ} (hX : ConvergesAt (T.zcoeff X) (T.ptRad ξ))
    (hY : ConvergesAt (T.zcoeff Y) (T.ptRad ξ)) :
    T.ptE hξ (X + Y) = T.ptE hξ X + T.ptE hξ Y := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hXY := T.convergesAt_zcoeff_add hr0 hr1 hX hY
  set P := fun N => T.partialSum X N
  set Q := fun N => T.partialSum Y N
  set S := fun N => T.partialSum (X + Y) N
  have hD : ∀ N, T.ptE hξ (S N) = T.ptE hξ (P N) + T.ptE hξ (Q N) + T.ptE hξ (S N - P N - Q N) := by
    intro N
    have bP := T.isBddElt_partialSum X N
    have bQ := T.isBddElt_partialSum Y N
    have bS := T.isBddElt_partialSum (X + Y) N
    rw [← T.ptE_add_of_bdd hξ bP bQ, ← T.ptE_add_of_bdd hξ (bP.add T bQ) ((bS.sub T bP).sub T bQ)]
    congr 1; ring
  have ta := T.tendsto_gaussNorm_sub_partialSum hr0 hXY
  have tb := T.tendsto_gaussNorm_sub_partialSum hr0 hX
  have tc := T.tendsto_gaussNorm_sub_partialSum hr0 hY
  have hDlim : Tendsto (fun N => T.ptE hξ (S N - P N - Q N)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmax : Tendsto (fun N : ℕ => max (max (gaussNorm (T.zcoeff (X + Y - S N)) (T.ptRad ξ))
        (gaussNorm (T.zcoeff (X - P N)) (T.ptRad ξ))) (gaussNorm (T.zcoeff (Y - Q N)) (T.ptRad ξ)))
        atTop (𝓝 0) := by
      simpa using (ta.max tb).max tc
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmax
    have ca := T.convergesAt_sub_partialSum hr0 hXY N
    have cb := T.convergesAt_sub_partialSum hr0 hX N
    have cc := T.convergesAt_sub_partialSum hr0 hY N
    have e : S N - P N - Q N = -(X + Y - S N) + (X - P N) + (Y - Q N) := by ring
    rw [e]
    have can := T.convergesAt_zcoeff_neg hr0 hr1 ca
    have c1 := T.convergesAt_zcoeff_add hr0 hr1 can cb
    refine (T.norm_ptE_le hξ (T.convergesAt_zcoeff_add hr0 hr1 c1 cc)).trans ?_
    refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le c1 cc).trans (max_le_max ?_ le_rfl)
    refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le can cb).trans (max_le_max ?_ le_rfl)
    rw [T.gaussNorm_zcoeff_neg hr0 hr1 ca]
  have hlim := ((T.tendsto_ptE_partialSum hξ hX).add (T.tendsto_ptE_partialSum hξ hY)).add hDlim
  rw [add_zero] at hlim
  refine tendsto_nhds_unique (T.tendsto_ptE_partialSum hξ hXY) ?_
  refine hlim.congr fun N => ?_
  exact (hD N).symm

theorem ptE_mul {X Y : Γ} (hX : ConvergesAt (T.zcoeff X) (T.ptRad ξ))
    (hY : ConvergesAt (T.zcoeff Y) (T.ptRad ξ)) :
    T.ptE hξ (X * Y) = T.ptE hξ X * T.ptE hξ Y := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hXY := T.convergesAt_zcoeff_mul hr0 hr1 hX hY
  set P := fun N => T.partialSum X N
  set Q := fun N => T.partialSum Y N
  set S := fun N => T.partialSum (X * Y) N
  have hD : ∀ N, T.ptE hξ (S N) = T.ptE hξ (P N) * T.ptE hξ (Q N) + T.ptE hξ (S N - P N * Q N) := by
    intro N
    have bP := T.isBddElt_partialSum X N
    have bQ := T.isBddElt_partialSum Y N
    have bS := T.isBddElt_partialSum (X * Y) N
    rw [← T.ptE_mul_of_bdd hξ bP bQ, ← T.ptE_add_of_bdd hξ (bP.mul T bQ) (bS.sub T (bP.mul T bQ))]
    congr 1; ring
  have ta := T.tendsto_gaussNorm_sub_partialSum hr0 hXY
  have tb := T.tendsto_gaussNorm_sub_partialSum hr0 hX
  have tc := T.tendsto_gaussNorm_sub_partialSum hr0 hY
  have hDlim : Tendsto (fun N => T.ptE hξ (S N - P N * Q N)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmax : Tendsto (fun N : ℕ => max (max (gaussNorm (T.zcoeff (X * Y - S N)) (T.ptRad ξ))
        (gaussNorm (T.zcoeff (X - P N)) (T.ptRad ξ) * gaussNorm (T.zcoeff Y) (T.ptRad ξ)))
        (gaussNorm (T.zcoeff X) (T.ptRad ξ) * gaussNorm (T.zcoeff (Y - Q N)) (T.ptRad ξ)))
        atTop (𝓝 0) := by
      simpa using (ta.max (tb.mul_const _)).max (tc.const_mul _)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmax
    have ca := T.convergesAt_sub_partialSum hr0 hXY N
    have cb := T.convergesAt_sub_partialSum hr0 hX N
    have cc := T.convergesAt_sub_partialSum hr0 hY N
    have cP := T.convergesAt_partialSum' hr0 hX N
    have e : S N - P N * Q N = -(X * Y - S N) + (X - P N) * Y + P N * (Y - Q N) := by ring
    rw [e]
    have can := T.convergesAt_zcoeff_neg hr0 hr1 ca
    have cbY := T.convergesAt_zcoeff_mul hr0 hr1 cb hY
    have cPc := T.convergesAt_zcoeff_mul hr0 hr1 cP cc
    have c1 := T.convergesAt_zcoeff_add hr0 hr1 can cbY
    refine (T.norm_ptE_le hξ (T.convergesAt_zcoeff_add hr0 hr1 c1 cPc)).trans ?_
    refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le c1 cPc).trans (max_le_max ?_ ?_)
    · refine (T.gaussNorm_zcoeff_add_le hr0 hr1.le can cbY).trans (max_le_max ?_ ?_)
      · rw [T.gaussNorm_zcoeff_neg hr0 hr1 ca]
      · rw [T.gaussNorm_zcoeff_mul hr0 hr1 cb hY]
    · rw [T.gaussNorm_zcoeff_mul hr0 hr1 cP cc]
      exact mul_le_mul_of_nonneg_right (T.gaussNorm_partialSum_le hr0 hX N) (gaussNorm_nonneg hr0)
  have hlim := ((T.tendsto_ptE_partialSum hξ hX).mul (T.tendsto_ptE_partialSum hξ hY)).add hDlim
  rw [add_zero] at hlim
  refine tendsto_nhds_unique (T.tendsto_ptE_partialSum hξ hXY) ?_
  refine hlim.congr fun N => ?_
  exact (hD N).symm

theorem ptE_neg {X : Γ} (hX : ConvergesAt (T.zcoeff X) (T.ptRad ξ)) :
    T.ptE hξ (-X) = -T.ptE hξ X := by
  have hn := T.convergesAt_zcoeff_neg (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ) hX
  have := T.ptE_add hξ hX hn
  rw [add_neg_cancel, ptE_zero] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem ptE_ξ : T.ptE hξ (ξ : Γ) = 0 := by
  rw [T.ptE_int hξ ξ.2]
  have : T.toUntilt ξ ⟨(ξ : Γ), ξ.2⟩ = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  rw [this, map_zero]

def ptEvalB (b : T.B) : T.UntiltField hξ := T.ptEvalSeq hξ (T.coeffB b)

theorem ptEvalB_eq {b : T.B} {X : Γ} {N : ℕ}
    (h : b * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B X) :
    T.ptEvalB hξ b = T.ptPi hξ ^ (-(N : ℤ)) * T.ptE hξ X := by
  rw [ptEvalB, T.coeffB_eq h, ptEvalSeq_shift]; rfl

theorem ptEvalB_algebraMap (X : Γ) : T.ptEvalB hξ (algebraMap Γ T.B X) = T.ptE hξ X := by
  rw [T.ptEvalB_eq hξ (X := X) (N := 0) (by simp)]; simp

theorem convergesAt_of_eq {b : T.B} {X : Γ} {N : ℕ}
    (h : b * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B X) {ρ : ℝ} (hρ : 0 < ρ) :
    ConvergesAt (T.coeffB b) ρ ↔ ConvergesAt (T.zcoeff X) ρ := by
  rw [T.coeffB_eq h, convergesAt_shift_iff hρ]

theorem norm_ptEvalB_le {b : T.B} (hb : ConvergesAt (T.coeffB b) (T.ptRad ξ)) :
    ‖T.ptEvalB hξ b‖ ≤ gaussNorm (T.coeffB b) (T.ptRad ξ) := T.norm_ptEvalSeq_le hξ hb

theorem ptEvalB_add {b c : T.B} (hb : ConvergesAt (T.coeffB b) (T.ptRad ξ))
    (hc : ConvergesAt (T.coeffB c) (T.ptRad ξ)) :
    T.ptEvalB hξ (b + c) = T.ptEvalB hξ b + T.ptEvalB hξ c := by
  obtain ⟨x, y, N, hx, hy⟩ := T.exists_common b c
  have hxy : (b + c) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (x + y) := by
    rw [add_mul, hx, hy, map_add]
  have hr0 := T.ptRad_pos' hξ
  rw [T.ptEvalB_eq hξ hx, T.ptEvalB_eq hξ hy, T.ptEvalB_eq hξ hxy,
    T.ptE_add hξ ((T.convergesAt_of_eq hx hr0).1 hb) ((T.convergesAt_of_eq hy hr0).1 hc), mul_add]

theorem ptEvalB_mul {b c : T.B} (hb : ConvergesAt (T.coeffB b) (T.ptRad ξ))
    (hc : ConvergesAt (T.coeffB c) (T.ptRad ξ)) :
    T.ptEvalB hξ (b * c) = T.ptEvalB hξ b * T.ptEvalB hξ c := by
  obtain ⟨x, y, N, hx, hy⟩ := T.exists_common b c
  have hxy : (b * c) * algebraMap Γ T.B T.π ^ (N + N) = algebraMap Γ T.B (x * y) := by
    rw [pow_add, map_mul, ← hx, ← hy]; ring
  have hr0 := T.ptRad_pos' hξ
  rw [T.ptEvalB_eq hξ hx, T.ptEvalB_eq hξ hy, T.ptEvalB_eq hξ hxy,
    T.ptE_mul hξ ((T.convergesAt_of_eq hx hr0).1 hb) ((T.convergesAt_of_eq hy hr0).1 hc)]
  push_cast
  rw [neg_add, zpow_add₀ (T.ptPi_ne_zero hξ)]
  ring

theorem ptEvalB_one : T.ptEvalB hξ 1 = 1 := by
  rw [← map_one (algebraMap Γ T.B), ptEvalB_algebraMap, ptE_one]

theorem ptEvalB_zero : T.ptEvalB hξ 0 = 0 := by
  rw [← map_zero (algebraMap Γ T.B), ptEvalB_algebraMap, ptE_zero]

theorem ptEvalB_ξ : T.ptEvalB hξ (algebraMap Γ T.B ξ) = 0 := by
  rw [ptEvalB_algebraMap, ptE_ξ]

def ptRadIoo : Set.Ioo (0 : ℝ) 1 := ⟨T.ptRad ξ, T.ptRad_pos' hξ, T.ptRad_lt_one' hξ⟩

def ptEvalEcon : T.Econ (T.ptRadIoo hξ) →+* T.UntiltField hξ where
  toFun b := T.ptEvalB hξ b
  map_one' := T.ptEvalB_one hξ
  map_mul' b c := T.ptEvalB_mul hξ b.2 c.2
  map_zero' := T.ptEvalB_zero hξ
  map_add' b c := T.ptEvalB_add hξ b.2 c.2

variable {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ ≤ ρ0)

def ptRadIoc : Set.Ioc (0 : ℝ) ρ0 := ⟨T.ptRad ξ, T.ptRad_pos' hξ, hr⟩

def ptEvalEconOf : T.Econ ρ0 →+* T.UntiltField hξ :=
  (T.ptEvalEcon hξ).comp (Subring.inclusion (T.Econ_anti (ρ := ρ0) (ρ' := T.ptRadIoo hξ) hr))

theorem ptEvalEconOf_apply (b : T.Econ ρ0) : T.ptEvalEconOf hξ hr b = T.ptEvalB hξ b := rfl

theorem uniformContinuous_ptEvalEconOf : UniformContinuous (T.ptEvalEconOf hξ hr) := by
  refine uniformContinuous_iInf_dom (i := T.ptRadIoc hξ hr) ?_
  refine (@Metric.uniformContinuous_iff _ _
    (T.gaussSeminorm ρ0 (T.ptRadIoc hξ hr)).toSeminormedRing.toPseudoMetricSpace _ _).2
    fun ε hε => ⟨ε, hε, fun {a b} hab => ?_⟩
  rw [dist_uniformAt'] at hab
  rw [dist_eq_norm, ← map_sub, ptEvalEconOf_apply]
  have hc : ConvergesAt (T.coeffB ((a - b : T.Econ ρ0) : T.B)) (T.ptRad ξ) :=
    T.convergesAt_rad ρ0 (a - b) (T.ptRadIoc hξ hr)
  refine (T.norm_ptEvalB_le hξ hc).trans_lt ?_
  exact hab

def ptEval : T.RobbaExt ρ0 →+* T.UntiltField hξ :=
  Completion.extensionHom (T.ptEvalEconOf hξ hr) (T.uniformContinuous_ptEvalEconOf hξ hr).continuous

theorem ptEval_coe (b : T.Econ ρ0) : T.ptEval hξ hr (b : T.RobbaExt ρ0) = T.ptEvalB hξ b :=
  Completion.extensionHom_coe _ _ b

theorem continuous_ptEval : Continuous (T.ptEval hξ hr) := Completion.continuous_extension

theorem norm_ptEval_le (x : T.RobbaExt ρ0) :
    ‖T.ptEval hξ hr x‖ ≤ T.extNorm ρ0 (T.ptRadIoc hξ hr) x :=
  Completion.induction_on x
    (isClosed_le ((T.continuous_ptEval hξ hr).norm) (T.continuous_extNorm _))
    fun b => by
      rw [ptEval_coe, extNorm_coe]
      exact T.norm_ptEvalB_le hξ (T.convergesAt_rad ρ0 b (T.ptRadIoc hξ hr))

theorem exists_radii_of_mem_uniformity {W : Set (T.RobbaExt ρ0 × T.RobbaExt ρ0)}
    (hW : W ∈ uniformity (T.RobbaExt ρ0)) :
    ∃ I : Set (Set.Ioc (0 : ℝ) ρ0), I.Finite ∧ ∃ ε : Set.Ioc (0 : ℝ) ρ0 → ℝ, (∀ i, 0 < ε i) ∧
      ∀ u v : T.RobbaExt ρ0, (∀ i ∈ I, T.extNorm ρ0 i (u - v) < ε i) → (u, v) ∈ W := by
  classical
  obtain ⟨W', ⟨hW'u, hW'c⟩, hW'W⟩ := (uniformity_hasBasis_closed.mem_iff).1 hW
  have hU := Filter.mem_map.1 ((Completion.uniformContinuous_coe (α := T.Econ ρ0)) hW'u)
  have hiInf : uniformity (T.Econ ρ0) = ⨅ ρ, @uniformity _ (T.uniformAt ρ0 ρ) := iInf_uniformity
  rw [hiInf] at hU
  obtain ⟨I, hIfin, V', hV', hUeq⟩ := Filter.mem_iInf.1 hU
  have hε : ∀ i : I, ∃ ε > 0, ∀ {a b : T.Econ ρ0},
      @dist _ (T.gaussSeminorm ρ0 i).toSeminormedRing.toPseudoMetricSpace.toDist a b < ε →
        (a, b) ∈ V' i := fun i =>
    (@Metric.mem_uniformity_dist _ (T.gaussSeminorm ρ0 i).toSeminormedRing.toPseudoMetricSpace
      (V' i)).1 (hV' i)
  choose ε hεpos hεV using hε
  haveI : Finite I := hIfin.to_subtype
  refine ⟨I, hIfin, fun i => if h : i ∈ I then ε ⟨i, h⟩ else 1, fun i => ?_, fun u v huv => hW'W ?_⟩
  · dsimp only
    split_ifs with h
    · exact hεpos _
    · exact one_pos
  have huv' : ∀ i : I, T.extNorm ρ0 i (u - v) < ε i := fun i => by
    have := huv i i.2
    simp only [dif_pos i.2] at this
    exact this
  show (u, v) ∈ W'
  rw [← hW'c.closure_eq, mem_closure_iff_nhds]
  intro t ht
  obtain ⟨O1, hO1, O2, hO2, hO⟩ := mem_nhds_prod_iff.1 ht
  have hO1' : O1 ∩ ⋂ i : I, {a : T.RobbaExt ρ0 | T.extNorm ρ0 i (a - u) < ε i} ∈ 𝓝 u := by
    refine Filter.inter_mem hO1 (Filter.iInter_mem.2 fun i => IsOpen.mem_nhds ?_ ?_)
    · exact isOpen_lt ((T.continuous_extNorm _).comp (continuous_id.sub continuous_const))
        continuous_const
    · simp only [Set.mem_setOf_eq, sub_self, extNorm_zero]; exact hεpos i
  have hO2' : O2 ∩ ⋂ i : I, {b : T.RobbaExt ρ0 | T.extNorm ρ0 i (v - b) < ε i} ∈ 𝓝 v := by
    refine Filter.inter_mem hO2 (Filter.iInter_mem.2 fun i => IsOpen.mem_nhds ?_ ?_)
    · exact isOpen_lt ((T.continuous_extNorm _).comp (continuous_const.sub continuous_id))
        continuous_const
    · simp only [Set.mem_setOf_eq, sub_self, extNorm_zero]; exact hεpos i
  obtain ⟨a, ha⟩ := Completion.denseRange_coe.mem_nhds hO1'
  obtain ⟨b, hb⟩ := Completion.denseRange_coe.mem_nhds hO2'
  refine ⟨((a : T.RobbaExt ρ0), (b : T.RobbaExt ρ0)), hO ⟨ha.1, hb.1⟩, ?_⟩
  have hmem : (a, b) ∈ (fun q : T.Econ ρ0 × T.Econ ρ0 =>
      ((q.1 : T.RobbaExt ρ0), (q.2 : T.RobbaExt ρ0))) ⁻¹' W' := by
    rw [hUeq, Set.mem_iInter]
    intro i
    refine hεV i ?_
    rw [dist_uniformAt]
    have h1 := Set.mem_iInter.1 ha.2 i
    have h2 := Set.mem_iInter.1 hb.2 i
    simp only [Set.mem_setOf_eq] at h1 h2
    have e : (a : T.RobbaExt ρ0) - b = ((a : T.RobbaExt ρ0) - u) + (u - v) + (v - b) := by ring
    rw [e]
    refine (T.extNorm_add_le _ _ _).trans_lt (max_lt ?_ h2)
    exact (T.extNorm_add_le _ _ _).trans_lt (max_lt h1 (huv' i))
  exact hmem

theorem tendsto_of_extNorm {z : ℕ → T.RobbaExt ρ0} {x : T.RobbaExt ρ0}
    (h : ∀ ρ, Tendsto (fun j => T.extNorm ρ0 ρ (x - z j)) atTop (𝓝 0)) :
    Tendsto z atTop (𝓝 x) := by
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨V, hV, hVs⟩ := UniformSpace.mem_nhds_iff.1 hs
  obtain ⟨I, hIfin, ε, hεpos, hε⟩ := T.exists_radii_of_mem_uniformity hV
  have hev : ∀ᶠ j in atTop, ∀ i ∈ I, T.extNorm ρ0 i (x - z j) < ε i :=
    (hIfin.eventually_all).2 fun i _ => (h i).eventually (gt_mem_nhds (hεpos i))
  filter_upwards [hev] with j hj
  exact hVs (hε x (z j) hj)

theorem cauchySeq_of_extNorm {z : ℕ → T.RobbaExt ρ0}
    (h : ∀ ρ ε, 0 < ε → ∃ J, ∀ j ≥ J, ∀ k ≥ J, T.extNorm ρ0 ρ (z j - z k) < ε) :
    CauchySeq z := by
  rw [cauchySeq_iff']
  intro V hV
  obtain ⟨I, hIfin, ε, hεpos, hε⟩ := T.exists_radii_of_mem_uniformity hV
  have hev : ∀ᶠ q in (atTop : Filter (ℕ × ℕ)), ∀ i ∈ I, T.extNorm ρ0 i (z q.1 - z q.2) < ε i := by
    refine (hIfin.eventually_all).2 fun i _ => ?_
    obtain ⟨J, hJ⟩ := h i (ε i) (hεpos i)
    exact (Filter.eventually_atTop_prod_self'
      (p := fun q : ℕ × ℕ => T.extNorm ρ0 i (z q.1 - z q.2) < ε i)).2 ⟨J, fun j hj k hk => hJ j hj k hk⟩
  filter_upwards [hev] with q hq
  exact hε _ _ hq

end TeichLift

end GroundTheory.PAdicHodge
