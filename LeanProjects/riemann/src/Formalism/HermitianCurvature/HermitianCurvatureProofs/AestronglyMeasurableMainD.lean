import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoSmulCocompact

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section abar

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def abar (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : ℝ := ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖

theorem abar_nonneg (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : 0 ≤ abar s ε bt D := Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma norm_psi_lemma (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  simp [G.psi, Complex.norm_exp]

theorem norm_mainD_le (s : ℕ) (β ε : ℂ) (bt : ℂ → H) (x D : ℂ) :
    ‖mainD s β ε bt x D‖ ≤ abar s ε bt D := by
  unfold mainD abar
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  rw [norm_smul, norm_psi_lemma, one_mul]

theorem mainD_ae_eq {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (x : ℂ) :
    mainD s β ε bt x =ᵐ[volume] fun D => ∑ k ∈ Finset.range s,
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D)) := by
  have h0 : ∀ᵐ D : ℂ ∂volume, D ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with D hD
  unfold mainD
  rw [sum_rootSet_eq_range hs (mul_ne_zero hε hD)]

theorem abar_ae_eq {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) :
    abar s ε bt =ᵐ[volume] fun D => ∑ k ∈ Finset.range s, ‖bt (NthRootMeasurability.R s k (ε * D))‖ := by
  have h0 : ∀ᵐ D : ℂ ∂volume, D ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with D hD
  unfold abar
  rw [sum_rootSet_eq_range hs (mul_ne_zero hε hD)]

private lemma measurable_R_lemma (s k : ℕ) : Measurable (NthRootMeasurability.R s k) := by
  unfold NthRootMeasurability.R
  exact measurable_const.mul (measurable_id.pow_const _)

private lemma continuous_psi_lemma_2 (β : ℂ) : Continuous (G.psi β) := by
  unfold G.psi
  fun_prop

theorem aestronglyMeasurable_mainD {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) (x : ℂ) : AEStronglyMeasurable (mainD s β ε bt x) volume := by
  refine AEStronglyMeasurable.congr (StronglyMeasurable.aestronglyMeasurable ?_)
    (mainD_ae_eq hs β hε bt x).symm
  have hk : ∀ k ∈ Finset.range s, StronglyMeasurable (fun D : ℂ =>
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D))) := by
    intro k _
    have hR : Measurable fun D : ℂ => NthRootMeasurability.R s k (ε * D) :=
      (measurable_R_lemma s k).comp (measurable_const.mul measurable_id)
    have hp : Measurable fun D : ℂ => G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) :=
      (continuous_psi_lemma_2 β).measurable.comp ((measurable_const.mul hR).mul measurable_const)
    exact hp.stronglyMeasurable.smul (hbt.comp_measurable hR)
  have := Finset.stronglyMeasurable_sum (Finset.range s) hk
  convert this using 1
  funext D
  simp only [Finset.sum_apply]

theorem aestronglyMeasurable_abar {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ε ≠ 0) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) : AEStronglyMeasurable (abar s ε bt) volume := by
  refine AEStronglyMeasurable.congr (StronglyMeasurable.aestronglyMeasurable ?_)
    (abar_ae_eq hs hε bt).symm
  have hk : ∀ k ∈ Finset.range s, StronglyMeasurable (fun D : ℂ => ‖bt (NthRootMeasurability.R s k (ε * D))‖) := by
    intro k _
    have hR : Measurable fun D : ℂ => NthRootMeasurability.R s k (ε * D) :=
      (measurable_R_lemma s k).comp (measurable_const.mul measurable_id)
    exact (hbt.comp_measurable hR).norm
  have := Finset.stronglyMeasurable_sum (Finset.range s) hk
  convert this using 1
  funext D
  simp only [Finset.sum_apply]

theorem card_rootSet_le (s : ℕ) (a : ℂ) : (G.rootSet s a).card ≤ s := by
  unfold G.rootSet
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots s a)

theorem jac_norm_bz {s : ℕ} {ε : ℂ} (hε : ‖ε‖ = 1) (bt : ℂ → H) (z : ℂ) :
    ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • ‖bt z‖ ^ 2 = ‖bz s bt z‖ ^ 2 := by
  simp only [bz, norm_smul, norm_mul, norm_inv, hε, inv_one, one_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul, abs_norm]
  rw [abs_of_nonneg (by positivity)]
  ring

theorem memLp_abar {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H} (hbt : StronglyMeasurable bt)
    (hb : MemLp (bz s bt) 2 volume) :
    MemLp (abar s ε bt) 2 volume ∧ ∫ D, abar s ε bt D ^ 2 ≤ s * ∫ z, ‖bz s bt z‖ ^ 2 := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hb2 : Integrable (fun z => ‖bz s bt z‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hb.1).1 hb
  have hF : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • ‖bt z‖ ^ 2) := by
    simp_rw [jac_norm_bz hε bt]; exact hb2
  obtain ⟨hGi, hGeq⟩ := integral_sum_rootSet s hs ε hε0 (fun z => ‖bt z‖ ^ 2) hF
  have hpt : ∀ D, abar s ε bt D ^ 2 ≤ s * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 := by
    intro D
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_rootSet_le s _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hm := aestronglyMeasurable_abar hs hε0 hbt
  have hsq : Integrable (fun D => abar s ε bt D ^ 2) := by
    refine Integrable.mono' (hGi.const_mul s) (hm.pow 2) (Eventually.of_forall fun D => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt D
  refine ⟨(memLp_two_iff_integrable_sq hm).2 hsq, ?_⟩
  calc ∫ D, abar s ε bt D ^ 2 ≤ ∫ D, (s : ℝ) * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 :=
        integral_mono hsq (hGi.const_mul s) hpt
    _ = s * ∫ z, ‖bz s bt z‖ ^ 2 := by
        rw [integral_const_mul, hGeq]
        simp_rw [jac_norm_bz hε bt]

theorem memLp_mainD {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) (hb : MemLp (bz s bt) 2 volume) (x : ℂ) :
    MemLp (mainD s β ε bt x) 2 volume := by
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
  refine (memLp_abar hs hε hbt hb).1.of_le (aestronglyMeasurable_mainD hs β hε0 hbt x)
    (ae_of_all _ fun D => ?_)
  rw [Real.norm_of_nonneg (abar_nonneg s ε bt D)]
  exact norm_mainD_le s β ε bt x D

end abar

section moving

theorem dil_dominator {α : Type} {l : Filter α} (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) (lam : α → ℂ)
    (hlam : Tendsto lam l (𝓝 1)) :
    (∀ a D, ‖lam a‖ * ab (lam a * D) ≤ ab D + |‖lam a‖ * ab (lam a * D) - ab D|) ∧
    (∀ᶠ a in l, MemLp (fun D => |‖lam a‖ * ab (lam a * D) - ab D|) 2 volume) ∧
    Tendsto (fun a => ∫ D, |‖lam a‖ * ab (lam a * D) - ab D| ^ 2) l (𝓝 0) := by
  refine ⟨fun a D => by linarith [le_abs_self (‖lam a‖ * ab (lam a * D) - ab D)], ?_, ?_⟩
  · filter_upwards [hlam.eventually_ne one_ne_zero] with a ha
    exact (((memLp_comp_mul hab (lam a) ha).const_mul ‖lam a‖).sub hab).abs
  · have h := (tendsto_dil_real ab hab).comp hlam
    refine h.congr fun a => ?_
    simp only [Function.comp_apply, sq_abs]

end moving

section cut

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mainD_indicator {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (Q : Set ℂ)
    (x D : ℂ) :
    mainD s β ε ({z | ε⁻¹ * z ^ s ∈ Q}.indicator bt) x D = Q.indicator (mainD s β ε bt x) D := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs
  have hroot : ∀ z ∈ G.rootSet s (ε * D), ε⁻¹ * z ^ s = D := by
    intro z hz
    have hz' : z ^ s = ε * D := by
      simpa [G.rootSet, Polynomial.mem_nthRoots hs0] using hz
    rw [hz', ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
  unfold mainD
  by_cases hD : D ∈ Q
  · rw [Set.indicator_of_mem hD]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Set.indicator_of_mem]
    show ε⁻¹ * z ^ s ∈ Q
    rw [hroot z hz]; exact hD
  · rw [Set.indicator_of_notMem hD]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [Set.indicator_of_notMem, smul_zero]
    show ε⁻¹ * z ^ s ∉ Q
    rw [hroot z hz]; exact hD

theorem bz_indicator (s : ℕ) (bt : ℂ → H) (Qz : Set ℂ) :
    bz s (Qz.indicator bt) = Qz.indicator (bz s bt) := by
  funext z
  by_cases hz : z ∈ Qz
  · simp [bz, Set.indicator_of_mem hz]
  · simp [bz, Set.indicator_of_notMem hz]

end cut

end

end Formalism.FourierDecayAlt.P.PBK
