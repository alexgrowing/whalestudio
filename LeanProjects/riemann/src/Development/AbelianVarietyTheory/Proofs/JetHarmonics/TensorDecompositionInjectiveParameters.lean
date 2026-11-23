import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasicStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosureStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionParameters

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensOrth

variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem hh_smul (Γ : Matrix ι ι ℂ) (R : Rep k r) (a b : ℂ) (x y : ι → R.H) :
    hh Γ R (fun c => a • x c) (fun c => b • y c) = a * star b * hh Γ R x y := by
  simp only [hh, inner_smul_left, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (x : ι → R.H) (y : κ → ι → R.H) :
    hh Γ R x (fun c => ∑ J, y J c) = ∑ J, hh Γ R x (y J) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem hh_star (Γ : Matrix ι ι ℂ) (hΓ : Γᴴ = Γ) (R : Rep k r) (x y : ι → R.H) :
    star (hh Γ R x y) = hh Γ R y x := by
  simp only [hh, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (Γ j i) = Γ i j := by
    have := congrFun (congrFun hΓ i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [h]
  congr 1
  exact inner_conj_symm _ _

theorem eq_zero_of_hh (Γ : Matrix ι ι ℂ) (hΓ : Γ * Γ = 1) (R : Rep k r) (x : ι → R.H)
    (h : hh Γ R x (fun c => ∑ j, Γ c j • x j) = 0) (c : ι) : x c = 0 := by
  set z : ι → R.H := fun c => ∑ j, Γ c j • x j with hz
  have h1 : hh Γ R x z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    unfold hh
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ⟪z i, z i⟫_ℂ = ∑ j, Γ i j * ⟪z i, x j⟫_ℂ := by
      conv_lhs => enter [3]; rw [hz]
      simp only [inner_sum, inner_smul_right]
    rw [← this, inner_self_eq_norm_sq_to_K]
    rfl
  rw [h1, Complex.ofReal_eq_zero] at h
  have h2 : ∀ i, z i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖z i‖)).1 h i (mem_univ _)
    simpa using this
  have h3 : ∑ i, Γ c i • z i = x c := by
    simp only [hz, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, hΓ, Matrix.one_apply]
    simp
  rw [← h3]
  simp [h2]

theorem SmMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have := hT.smul 0 0 R.smSub.zero_mem
  simpa using this

omit [DecidableEq ι] [DecidableEq κ] in
theorem raw_scale {ρ : Mx k r → Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
    {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} (h : TensRaw ρ R RI io pr)
    (a : κ → ℂ) (ha : ∀ I, a I ≠ 0)
    (h1 : ∀ I c, SmMap (RI I) R (fun v => a I • io I c v))
    (h2 : ∀ I c, SmMap R (RI I) (fun v => (a I)⁻¹ • pr I c v)) :
    TensRaw ρ R RI (fun I c v => a I • io I c v) (fun I c v => (a I)⁻¹ • pr I c v) where
  io_sm := h1
  pr_sm := h2
  io_eq := fun I g hg y hy => by
    funext c
    have := congrFun (h.io_eq I g hg y hy) c
    simp only [act] at this ⊢
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_comm]
  pr_eq := fun I g hg x hx => by
    rw [← Finset.smul_sum, ← Finset.smul_sum, map_smul, h.pr_eq I g hg x hx]
  sum_io_pr := fun x hx c => by
    rw [← h.sum_io_pr x hx c]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hm : ∑ d, pr I d (x d) ∈ (RI I).smSub :=
      Submodule.sum_mem _ fun d _ => (h.pr_sm I d).mem _ (hx d)
    rw [← Finset.smul_sum, (h.io_sm I c).smul _ _ hm, smul_smul, mul_inv_cancel₀ (ha I), one_smul]
  pr_io := fun I y hy => by
    conv_rhs => rw [← h.pr_io I y hy]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h.pr_sm I c).smul _ _ ((h.io_sm I c).mem _ hy), smul_smul, inv_mul_cancel₀ (ha I), one_smul]
  pr_io_ne := fun I J hIJ y hy => by
    have : ∀ c, (a I)⁻¹ • pr I c (a J • io J c y) = ((a I)⁻¹ * a J) • pr I c (io J c y) := fun c => by
      rw [(h.pr_sm I c).smul _ _ ((h.io_sm J c).mem _ hy), smul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h.pr_io_ne I J hIJ y hy, smul_zero]

theorem tensH_of_raw : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hinj hF hT
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : Poulsen := hH.2.2.2.2.2.1
  have hform := GlobalTheory.TensForm.pulledBack_isInvForm hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  have horth : ∀ I J, I ≠ J → ∀ y ∈ (RI I).sm, ∀ y' ∈ (RI J).sm,
      hh Γ R (fun c => io I c y) (fun c => io J c y') = 0 := by
    intro I J hIJ
    rcases (hP k r ε _ _ _ _ (hRI I) (hRI J)).2 _ (hform I J) with h | ⟨U, hU⟩
    · exact h
    · exact absurd (hinj (GlobalTheory.DSInequiv.param_eq_of_equiv hH k r ε _ _ _ _ (hRI I) (hRI J) U hU)) hIJ
  choose cI hc using fun I => (hP k r ε _ _ _ _ (hRI I) (hRI I)).1 _ (hform I I)
  have hunit : ∀ I, ∃ w ∈ (RI I).sm, ‖w‖ = 1 := fun I => by
    obtain ⟨-, -, -, -, h5, -, h7, ⟨w, hw, hwK, -⟩, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε _ _ (hRI I)
    exact ⟨w, h5 w (h7 w hwK), hw⟩
  have hreal : ∀ I, ((cI I).re : ℂ) = cI I := fun I => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have h1 := hc I w hw w hw
    have h2 := hh_star Γ hF.1 R (fun c => io I c w) (fun c => io I c w)
    rw [inner_self_eq_norm_sq_to_K, hn] at h1
    simp only [map_one, one_pow, mul_one] at h1
    rw [h1] at h2
    exact Complex.conj_eq_iff_re.1 h2
  have hne : ∀ I, cI I ≠ 0 := fun I h0 => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have hx : ∀ c, (∑ j, Γ c j • io I j w) ∈ R.smSub := fun c =>
      Submodule.sum_mem _ fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ hw)
    have hz : hh Γ R (fun c => io I c w) (fun c => ∑ j, Γ c j • io I j w) = 0 := by
      have e : (fun c => ∑ j, Γ c j • io I j w) =
          fun c => ∑ J, io J c (∑ e, pr J e (∑ j, Γ e j • io I j w)) :=
        funext fun c => (hT.sum_io_pr _ hx c).symm
      rw [e, hh_sum_right]
      refine Finset.sum_eq_zero fun J _ => ?_
      have hm : ∑ e, pr J e (∑ j, Γ e j • io I j w) ∈ (RI J).smSub :=
        Submodule.sum_mem _ fun e _ => (hT.pr_sm J e).mem _ (hx e)
      by_cases hIJ : I = J
      · subst hIJ
        have := hc I w hw _ hm
        rw [h0, zero_mul] at this
        exact this
      · exact horth I J hIJ w hw _ hm
    have h0' := eq_zero_of_hh Γ hF.2.1 R _ hz
    have h1 := hT.pr_io I w hw
    simp only [h0', SmMap_zero (hT.pr_sm I _), Finset.sum_const_zero] at h1
    rw [← h1, norm_zero] at hn
    exact zero_ne_one hn
  have hre : ∀ I, (cI I).re ≠ 0 := fun I h => hne I (by rw [← hreal I, h]; simp)
  have hsc : ∀ (m m' : Fin (2 * r + k + 1) → ℝ) (S S' : Rep k r), S.IsDS ε m → S'.IsDS ε m' →
      ∀ (T : S.H → S'.H) (a : ℂ), SmMap S S' T → SmMap S S' (fun v => a • T v) := by
    intro m m' S S' hS hS' T a h
    have := (GlobalTheory.T.smooth_maps_closure hK k r ε _ _ _ S S' S' hS hS' hS').2.2.1 T T (a - 1) h h
    simpa only [sub_smul, one_smul, sub_add_cancel] using this
  set a : κ → ℂ := fun I => (((Real.sqrt |(cI I).re|)⁻¹ : ℝ) : ℂ) with ha
  have hane : ∀ I, a I ≠ 0 := fun I => by
    simp only [ha, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (abs_pos.2 (hre I))).ne'
  refine ⟨fun I c v => a I • io I c v, fun I c v => (a I)⁻¹ • pr I c v,
    fun I => (cI I).re / |(cI I).re|, ⟨raw_scale hT a hane
      (fun I c => hsc _ _ _ _ (hRI I) hR _ _ (hT.io_sm I c))
      (fun I c => hsc _ _ _ _ hR (hRI I) _ _ (hT.pr_sm I c)), fun I => ?_, fun I y hy y' hy' => ?_,
      fun I J hIJ y hy y' hy' => ?_⟩⟩
  · rcases lt_or_gt_of_ne (hre I) with h | h
    · right
      rw [abs_of_neg h, div_neg, div_self (hre I)]
    · left
      rw [abs_of_pos h, div_self (hre I)]
  · have h1 := hc I y hy y' hy'
    rw [hh_smul, h1, ← mul_assoc]
    congr 1
    have h2 : (Real.sqrt |(cI I).re|)⁻¹ * (Real.sqrt |(cI I).re|)⁻¹ * (cI I).re = (cI I).re / |(cI I).re| := by
      rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_inv_mul]
    rw [← h2]
    simp only [ha, RCLike.star_def, Complex.conj_ofReal]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hreal I]
  · rw [hh_smul, horth I J hIJ y hy y' hy', mul_zero]

end GlobalTheory.TensOrth
