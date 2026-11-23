import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CardSupportLeAndSumTwoPowLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAC

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

section Asm

variable {ι : Type} [Fintype ι]

open Classical

theorem paU_zero (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : paU q 0 F = F := by
  funext v
  simp [paU, Hf]

theorem paTh_diff_le (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0) (hk0 : Y.ka 0 = 1)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    ‖paIP q (paTh Y q F) G - paIP q F G‖ ≤
      (2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
        ∑' γ : lat Y.b, (if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
          Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16))) * paN q F * paN q G := by
  obtain ⟨hBs, -⟩ := paTail hP hA Y hq hR0 hlat hR
  have hT := paTh_IP hP hA Y hq hR0 hlat hR hF hG
  have hg := hT.update 0 0
  have hf0 : Y.ka ((0 : lat Y.b) : EuclideanSpace ℂ ι) *
      paIP q (paU q ((0 : lat Y.b) : EuclideanSpace ℂ ι) F) G = paIP q F G := by
    simp [hk0, paU_zero]
  set K : ℝ := 2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) with hK
  set B : lat Y.b → ℝ := fun γ => if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
    Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16) with hB
  set g := Function.update (fun γ : lat Y.b => Y.ka γ * paIP q (paU q γ F) G) 0 0 with hgdef
  have hbound : ∀ γ, ‖g γ‖ ≤ K * B γ * paN q F * paN q G := by
    intro γ
    by_cases h : (γ : EuclideanSpace ℂ ι) = 0
    · have h0 : γ = 0 := Subtype.ext h
      subst h0
      simp [g, B]
    · have hne : γ ≠ 0 := fun h' => h (by rw [h']; rfl)
      rw [hgdef, Function.update_of_ne hne]
      simp only [B, if_neg h]
      rw [norm_mul, Y.ka_abs γ γ.2, one_mul]
      exact polynomial_translate_innerProduct_bound hq (γ : EuclideanSpace ℂ ι) hF hG
  have hsB : Summable fun γ => K * B γ * paN q F * paN q G :=
    ((hBs.mul_left K).mul_right (paN q F)).mul_right (paN q G)
  have hsg : Summable fun γ => ‖g γ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsB
  have heq : paIP q (paTh Y q F) G - paIP q F G = ∑' γ, g γ := by
    rw [hg.tsum_eq]
    simp only [hf0]
    ring
  rw [heq]
  calc ‖∑' γ, g γ‖ ≤ ∑' γ, ‖g γ‖ := norm_tsum_le_tsum_norm hsg
    _ ≤ ∑' γ, K * B γ * paN q F * paN q G := Summable.tsum_le_tsum hbound hsg hsB
    _ = (K * ∑' γ, B γ) * paN q F * paN q G := by
      rw [tsum_mul_right, tsum_mul_right, tsum_mul_left]

end Asm

section Asm2

variable {ι : Type} [Fintype ι]

open Classical

theorem paU_add (q : ℕ) (a : EuclideanSpace ℂ ι) (F G : EuclideanSpace ℂ ι → ℂ) :
    paU q a (F + G) = paU q a F + paU q a G := by
  funext v
  simp only [paU, Pi.add_apply]
  ring

theorem paU_smul (q : ℕ) (a : EuclideanSpace ℂ ι) (b : ℂ) (F : EuclideanSpace ℂ ι → ℂ) :
    paU q a (b • F) = b • paU q a F := by
  funext v
  simp only [paU, Pi.smul_apply, smul_eq_mul]
  ring

theorem paTh_data (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    Differentiable ℂ (paTh Y q F) ∧ (∀ v, Summable (fun γ : lat Y.b => Y.ka γ * paU q γ F v)) ∧
      ∀ α : ι →₀ ℕ, HasSum (fun γ : lat Y.b => Y.ka γ * paD α (paU q γ F)) (paD α (paTh Y q F)) := by
  have hb := fun R => paTh_bound hP hA Y hq hR0 hlat hR hF R
  have hcd : ∀ γ : lat Y.b, ContDiff ℂ (⊤ : ℕ∞) (fun v => Y.ka γ * paU q γ F v) :=
    fun γ => contDiff_const.mul (paU_contDiff (γ : EuclideanSpace ℂ ι) hF)
  obtain ⟨hd, hD⟩ := paD_tsum (fun γ : lat Y.b => fun v => Y.ka γ * paU q γ F v) hcd hb
  refine ⟨hd, fun v => ?_, fun α => ?_⟩
  · obtain ⟨u, hu, hub⟩ := hb ‖v‖
    exact Summable.of_norm_bounded hu (fun γ => hub γ v le_rfl)
  · convert hD α using 1
    · funext γ
      exact (paD_smul α _ (paU_contDiff (γ : EuclideanSpace ℂ ι) hF)).symm
    · rfl

end Asm2

section Asm3

variable {ι : Type} [Fintype ι]

open Classical

theorem propA_core (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hC : ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
      Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I))
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (h270 : 270 ≤ R0 ^ 2) (h90 : 90 * ((Fintype.card ι : ℝ) + c) ≤ R0 ^ 2)
    {j : EuclideanSpace ℂ ι → ℂ} (hj : j ∈ paPoly c) :
    ∃ β ∈ Y.Sec q, (∀ α ∈ paS c, paD α β = paD α j) ∧ Y.l2 q β ≤ 2 * (paIP q j j).re := by
  have hg0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2 := by linarith
  have hk0 : Y.ka 0 = 1 := by
    have h := hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    have h1 : ‖Y.ka 0‖ = 1 := Y.ka_abs 0 (Submodule.zero_mem _)
    have hne : Y.ka 0 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have h2 : Y.ka 0 * Y.ka 0 = Y.ka 0 * 1 := by
      simp only [add_zero] at h
      have hH : Hf (0 : EuclideanSpace ℂ ι) 0 = 0 := by simp [Hf]
      simp only [hH, Complex.zero_im, Complex.ofReal_zero, mul_zero, neg_zero, zero_mul,
        Complex.exp_zero, mul_one] at h
      rw [mul_one]
      exact h.symm
    exact mul_left_cancel₀ hne h2
  have hdata := fun {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) =>
    paTh_data hP hA Y hq hR0 hlat hR hF
  have hcd : ∀ {F : EuclideanSpace ℂ ι → ℂ}, F ∈ paPoly c → ContDiff ℂ (⊤ : ℕ∞) (paTh Y q F) :=
    fun hF => pa_contDiff_of_diff (hdata hF).1
  have hThAdd : ∀ {F G : EuclideanSpace ℂ ι → ℂ}, F ∈ paPoly c → G ∈ paPoly c →
      paTh Y q (F + G) = paTh Y q F + paTh Y q G := by
    intro F G hF hG
    funext v
    simp only [paTh, Pi.add_apply]
    rw [← Summable.tsum_add ((hdata hF).2.1 v) ((hdata hG).2.1 v)]
    congr 1
    funext γ
    rw [paU_add, Pi.add_apply, mul_add]
  have hThSmul : ∀ (a : ℂ) (F : EuclideanSpace ℂ ι → ℂ), paTh Y q (a • F) = a • paTh Y q F := by
    intro a F
    funext v
    simp only [paTh, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    congr 1
    funext γ
    rw [paU_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hJetAdd : ∀ {H1 H2 : EuclideanSpace ℂ ι → ℂ}, ContDiff ℂ (⊤ : ℕ∞) H1 →
      ContDiff ℂ (⊤ : ℕ∞) H2 → paJet c (H1 + H2) = paJet c H1 + paJet c H2 := by
    intro H1 H2 h1 h2
    unfold paJet
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [paD_add α h1 h2, add_div, add_smul]
  have hJetSmul : ∀ (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}, ContDiff ℂ (⊤ : ℕ∞) H →
      paJet c (a • H) = a • paJet c H := by
    intro a H h
    unfold paJet
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [paD_smul α a h, mul_div_assoc, mul_smul]
  let T : paPoly (ι := ι) c →ₗ[ℂ] paPoly (ι := ι) c :=
    { toFun := fun F => ⟨paJet c (paTh Y q F), paJet_mem c _⟩
      map_add' := fun F G => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [hThAdd F.2 G.2, hJetAdd (hcd F.2) (hcd G.2)]
      map_smul' := fun a F => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [hThSmul, hJetSmul a (hcd F.2)] }
  have hJ : ∀ {F G : EuclideanSpace ℂ ι → ℂ}, F ∈ paPoly c → G ∈ paPoly c →
      paIP q (paJet c (paTh Y q F)) G = paIP q (paTh Y q F) G := by
    intro F G hF hG
    rw [gaussianInner_jet_eq_sum hq _ hG]
    have h1 := paTh_IP hP hA Y hq hR0 hlat hR hF hG
    have h2 : ∀ γ : lat Y.b, Y.ka γ * paIP q (paU q γ F) G =
        ∑ α ∈ paS c, (Y.ka γ * paD α (paU q γ F)) / paFact α * paIP q (paMono α) G := by
      intro γ
      rw [gaussianInner_jet hq _ hF hG, gaussianInner_jet_eq_sum hq _ hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    have h3 : HasSum (fun γ : lat Y.b => ∑ α ∈ paS c,
        (Y.ka γ * paD α (paU q γ F)) / paFact α * paIP q (paMono α) G)
        (∑ α ∈ paS c, paD α (paTh Y q F) / paFact α * paIP q (paMono α) G) := by
      apply hasSum_sum
      intro α _
      exact (((hdata hF).2.2 α).div_const _).mul_right _
    rw [← funext h2] at h3
    exact h3.unique h1
  obtain ⟨hBs2, hBt⟩ := paTail hP hA Y hq hR0 hlat hR
  have hK0 : (0 : ℝ) ≤ 2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) := by positivity
  have hε := (mul_le_mul_of_nonneg_left hBt hK0).trans (paNum (Fintype.card ι) (c : ℝ) R0 hc0 h270 h90)
  have hclose : ∀ {F G : EuclideanSpace ℂ ι → ℂ}, F ∈ paPoly c → G ∈ paPoly c →
      ‖paIP q (paJet c (paTh Y q F)) G - paIP q F G‖ ≤ 1 / 2 * paN q F * paN q G := by
    intro F G hF hG
    rw [hJ hF hG]
    refine (paTh_diff_le hP hA Y hq hR0 hk0 hlat hR hF hG).trans ?_
    have hNF : 0 ≤ paN q F := Real.sqrt_nonneg _
    have hNG : 0 ≤ paN q G := Real.sqrt_nonneg _
    gcongr
  have hsq : ∀ F : EuclideanSpace ℂ ι → ℂ, paN q F ^ 2 = (paIP q F F).re := fun F =>
    Real.sq_sqrt (gaussianInner_self_re q F).2
  have hlow : ∀ {F : EuclideanSpace ℂ ι → ℂ}, F ∈ paPoly c →
      1 / 2 * paN q F ^ 2 ≤ (paIP q (paJet c (paTh Y q F)) F).re := by
    intro F hF
    have h1 := hclose hF hF
    have h2 := (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
    rw [Complex.sub_re] at h2
    have h3 := hsq F
    nlinarith
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro F hF0
    have h0 : paJet c (paTh Y q F) = 0 := congrArg Subtype.val hF0
    have h1 := hlow F.2
    rw [h0] at h1
    have h2 : paIP q (0 : EuclideanSpace ℂ ι → ℂ) F = 0 := by simp [paIP]
    rw [h2, Complex.zero_re] at h1
    have hN : paN q (F : EuclideanSpace ℂ ι → ℂ) = 0 := by
      have : 0 ≤ paN q (F : EuclideanSpace ℂ ι → ℂ) := Real.sqrt_nonneg _
      nlinarith
    exact Subtype.ext (paN_eq_zero hq F.2 hN)
  have : FiniteDimensional ℂ (paPoly (ι := ι) c) := paPoly_fd c
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨F, hFj⟩ := hsurj ⟨j, hj⟩
  have hFj' : paJet c (paTh Y q F) = j := congrArg Subtype.val hFj
  have hF := F.2
  refine ⟨paTh Y q F, paTh_sec Y hC (hdata hF).1 (hdata hF).2.1, fun α hα => ?_, ?_⟩
  · rw [← hFj']
    exact (paD_jet c _ hα).symm
  · rw [paUnfold hP hA Y hq hR0 hC hlat hR hF, ← hJ hF hF, hFj']
    have hl := hlow hF
    rw [hFj'] at hl
    have hcs := norm_gaussianInner_le hq hj hF
    have hre := Complex.re_le_norm (paIP q j (F : EuclideanSpace ℂ ι → ℂ))
    have hNF : 0 ≤ paN q (F : EuclideanSpace ℂ ι → ℂ) := Real.sqrt_nonneg _
    have hNj : 0 ≤ paN q j := Real.sqrt_nonneg _
    have hj2 := hsq j
    have hb : paN q (F : EuclideanSpace ℂ ι → ℂ) ≤ 2 * paN q j := by nlinarith
    nlinarith

end Asm3

theorem propA (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) : PropAStatement := by
  intro ι _ Y q c R0 hq hCoc hR0 hlat h270 h90 p hp
  obtain ⟨β, hβ, hjet, hl2⟩ := propA_core hP hA Y hq hR0 hCoc hlat h270 h90 (paPF_mem_paPoly hp)
  refine ⟨β, hβ, fun α hα => hjet α (mem_paS.2 hα), ?_⟩
  rw [gaussianInner_self q (paPF p), Complex.ofReal_re] at hl2
  have hnn : 0 ≤ ∫ v, ‖paPF p v‖ ^ 2 * paW q v :=
    integral_nonneg fun v => mul_nonneg (sq_nonneg _) (paW_pos q v).le
  calc Y.l2 q β ≤ 2 * ∫ v, ‖paPF p v‖ ^ 2 * paW q v := hl2
    _ ≤ 6 * ∫ v, ‖paPF p v‖ ^ 2 * paW q v := by linarith
    _ = _ := rfl

end

end ReciprocityTheory.ChartRestriction.G.I2
