import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSmoothCompactSupportHasSumLatticeTranslate

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory
namespace UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem hasSum_quot {G : Type} [Group G] (T : Subgroup G) [Finite T] (f : G ⧸ T → ℝ) (s : ℝ)
    (hf : HasSum f s) : HasSum (fun g : G => f (g : G ⧸ T) / Nat.card T) s := by
  classical
  have : Fintype T := Fintype.ofFinite T
  have hT : (Nat.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  let e : G ≃ (G ⧸ T) × T := Subgroup.groupEquivQuotientProdSubgroup
  have he : ∀ g : G, (e g).1 = (g : G ⧸ T) := fun g => rfl
  have hp : ∀ p : (G ⧸ T) × T, ((e.symm p : G) : G ⧸ T) = p.1 := fun p => by
    rw [← he, e.apply_symm_apply]
  have hfun : (fun g : G => f (g : G ⧸ T) / Nat.card T) ∘ e.symm =
      fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹ := by
    funext p
    simp only [Function.comp_apply, hp p, div_eq_mul_inv]
  have hg : HasSum (fun _ : T => (Nat.card T : ℝ)⁻¹) 1 := by
    have h0 := hasSum_fintype (fun _ : T => (Nat.card T : ℝ)⁻¹)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      mul_inv_cancel₀ hT] at h0
  have hprod : HasSum (fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹) s := by
    have hs1 : Summable fun q : G ⧸ T => ‖f q‖ := by
      simpa only [Real.norm_eq_abs] using hf.summable.abs
    have hs2 : Summable fun _ : T => ‖(Nat.card T : ℝ)⁻¹‖ := Summable.of_finite
    have hs : Summable fun p : (G ⧸ T) × T => f p.1 * (fun _ : T => (Nat.card T : ℝ)⁻¹) p.2 :=
      summable_mul_of_summable_norm (R := ℝ) (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hs1 hs2
    have h0 := HasSum.mul (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hf hg hs
    rwa [mul_one] at h0
  rw [← e.symm.hasSum_iff, hfun]
  exact hprod

variable {K : Type} [Field K] [NumberField K]

theorem contDiffAt_normAtPlace (w : InfinitePlace K) (x : mixedSpace K)
    (hx : normAtPlace w x ≠ 0) : ContDiffAt ℝ ∞ (fun y : mixedSpace K => normAtPlace w y) x := by
  rcases w.isReal_or_isComplex with hw | hw
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.1 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isReal hw y
    rw [normAtPlace_apply_of_isReal hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.2 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isComplex hw y
    rw [normAtPlace_apply_of_isComplex hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)

theorem contDiffAt_logMap (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    ContDiffAt ℝ ∞ (logMap (K := K)) x := by
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hnorm : ContDiffAt ℝ ∞ (fun y : mixedSpace K => mixedEmbedding.norm y) x := by
    have e : (fun y : mixedSpace K => mixedEmbedding.norm y) =
        fun y => ∏ w, normAtPlace w y ^ mult w := funext fun y => mixedEmbedding.norm_apply y
    rw [e]
    exact contDiffAt_prod fun w _ => (contDiffAt_normAtPlace w x (hN w)).pow _
  refine contDiffAt_pi.2 fun w => ?_
  simp only [logMap_apply]
  exact contDiffAt_const.mul (((contDiffAt_normAtPlace w.1 x (hN w.1)).log (hN w.1)).sub
    ((hnorm.log hx).mul contDiffAt_const))

private lemma le_of_mul_le_of_one_le' {m t B : ℝ} (hm : 1 ≤ m) (hB : 0 ≤ B) (h : m * t ≤ B) :
    t ≤ B := by
  rcases le_or_gt t 0 with ht | ht
  · exact ht.trans hB
  · nlinarith

theorem log_le (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) (w : InfinitePlace K) :
    Real.log (normAtPlace w x) ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ +
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹ := by
  classical
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hd0 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
  have hL : Real.log (mixedEmbedding.norm x) =
      ∑ v, (mult v : ℝ) * Real.log (normAtPlace v x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod (fun v _ => pow_ne_zero _ (hN v))]
    simp only [Real.log_pow]
  have hm : ∑ v : InfinitePlace K, (mult v : ℝ) = Module.finrank ℚ K := by
    rw [← sum_mult_eq, Nat.cast_sum]
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hpos : 0 ≤ ‖logMap x‖ := norm_nonneg _
  have hB : 0 ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ := by positivity
  have hle : ‖logMap x‖ ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ :=
    le_mul_of_one_le_left hpos hcard
  rw [← sub_le_iff_le_add]
  by_cases hw : w = w₀
  · subst hw
    set L := Real.log (mixedEmbedding.norm x)
    set d : ℝ := (Module.finrank ℚ K : ℝ)
    have h1 := Fintype.sum_eq_add_sum_subtype_ne
      (fun v => (mult v : ℝ) * Real.log (normAtPlace v x)) w₀
    have h2 := Fintype.sum_eq_add_sum_subtype_ne (fun v : InfinitePlace K => (mult v : ℝ)) w₀
    rw [← hL] at h1
    rw [hm] at h2
    have hS : ∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v =
        ∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ) * Real.log (normAtPlace v.1 x) -
          (∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ)) * (L * d⁻¹) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [logMap_apply]
      ring
    have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0.ne'
    have hkey : (mult (w₀ : InfinitePlace K) : ℝ) * (Real.log (normAtPlace w₀ x) - L * d⁻¹) =
        -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v := by
      rw [hS]
      linear_combination (-1 : ℝ) * h1 + (L * d⁻¹) * h2 - L * hdd
    have hSle : -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v ≤
        Fintype.card (InfinitePlace K) * ‖logMap x‖ := by
      refine (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      refine (Finset.sum_le_sum fun v _ => (show |logMap x v| ≤ ‖logMap x‖ from
        (Real.norm_eq_abs (logMap x v)).symm.trans_le (norm_le_pi_norm (logMap x) v))).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) hpos
    exact le_of_mul_le_of_one_le' one_le_mult hB (hkey.trans_le hSle)
  · have hv : logMap x ⟨w, hw⟩ = (mult w : ℝ) * (Real.log (normAtPlace w x) -
        Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) := logMap_apply x ⟨w, hw⟩
    refine le_of_mul_le_of_one_le' (one_le_mult (w := w)) hB ?_
    rw [← hv]
    exact (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le
      (norm_le_pi_norm (logMap x) ⟨w, hw⟩)).trans hle)

end UnitPartition

open UnitPartition NumberField.Units NumberField.Units.dirichletUnitTheorem in

theorem exists_smooth_homogeneous_hasSum_unit_smul : ∀ (K : Type) [Field K] [NumberField K], ∃ h : mixedSpace K → ℝ, ContDiffOn ℝ ∞ h {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ (t : ℝ) x, 0 < t → h (t • x) = h x) ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => h (u • x)) 1) ∧ (∀ a b : ℝ, 0 < a → ∃ C : Set (mixedSpace K), IsCompact C ∧ (∀ x ∈ C, mixedEmbedding.norm x ≠ 0) ∧ ∀ x, h x ≠ 0 → a ≤ mixedEmbedding.norm x → mixedEmbedding.norm x ≤ b → x ∈ C) := by
  intro K _ _
  obtain ⟨η, hη, hηc, hηs⟩ := exists_smooth_compactSupport_hasSum_lattice_translates
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) (unitLattice K)
  refine ⟨fun x => if mixedEmbedding.norm x = 0 then 0 else
    η (logMap x) / (Nat.card (torsion K) : ℝ), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : mixedEmbedding.norm x ≠ 0 := hx
    have hopen : IsOpen {y : mixedSpace K | mixedEmbedding.norm y ≠ 0} :=
      isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
    refine ContDiffAt.contDiffWithinAt ?_
    have hev : (fun y : mixedSpace K => if mixedEmbedding.norm y = 0 then 0 else
        η (logMap y) / (Nat.card (torsion K) : ℝ)) =ᶠ[nhds x]
        fun y => η (logMap y) / (Nat.card (torsion K) : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [if_neg hy]
    exact ((hη.contDiffAt.comp x (contDiffAt_logMap x hx')).div_const _).congr_of_eventuallyEq hev
  · intro t x ht
    have ht0 : t ≠ 0 := ht.ne'
    simp only [mixedEmbedding.norm_smul]
    by_cases hx : mixedEmbedding.norm x = 0
    · simp [hx]
    · have hne : |t| ^ Module.finrank ℚ K * mixedEmbedding.norm x ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (abs_ne_zero.2 ht0)) hx
      rw [if_neg hne, if_neg hx, logMap_real_smul hx ht0]
  · intro x hx
    let e : ((𝓞 K)ˣ ⧸ torsion K) ≃ unitLattice K :=
      Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv
    have hq : HasSum ((fun l : unitLattice K => η (logMap x + l)) ∘ e) 1 :=
      e.hasSum_iff.2 (hηs (logMap x))
    have hu := hasSum_quot (torsion K) _ 1 hq
    convert hu using 2 with u
    have hux : mixedEmbedding.norm (u • x) ≠ 0 := by rwa [norm_unit_smul]
    dsimp only
    rw [if_neg hux, logMap_unit_smul u hx, add_comm]
    simp only [Function.comp_apply, e, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      logEmbeddingEquiv_apply]
  · intro a b ha
    obtain ⟨R, hR⟩ := hηc.isCompact.isBounded.exists_norm_le
    refine ⟨Metric.closedBall 0 (Real.exp (Fintype.card (InfinitePlace K) * R +
        Real.log b * (Module.finrank ℚ K : ℝ)⁻¹)) ∩ {x | a ≤ mixedEmbedding.norm x},
      (isCompact_closedBall _ _).inter_right
        (isClosed_le continuous_const (mixedEmbedding.continuous_norm K)),
      fun x hx => (ha.trans_le hx.2).ne', fun x hx hax hxb => ⟨?_, hax⟩⟩
    have hx0 : mixedEmbedding.norm x ≠ 0 := (ha.trans_le hax).ne'
    dsimp only at hx
    rw [if_neg hx0] at hx
    have hηx : η (logMap x) ≠ 0 := fun h0 => hx (by rw [h0, zero_div])
    have hlog : ‖logMap x‖ ≤ R := hR _ (subset_tsupport _ hηx)
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => ?_
    have hNw : 0 < normAtPlace w x :=
      lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.1 hx0 w).symm
    rw [← Real.exp_log hNw]
    refine Real.exp_le_exp.2 ((log_le x hx0 w).trans (add_le_add
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)) ?_))
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (ha.trans_le hax) hxb) (by positivity)

end GlobalTheory
