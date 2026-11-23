import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGapAng

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap

open PGap

theorem gapAbs_of : Hilb → Design → Unfold → AEConst → GapAbs := by
  intro hH hD hU hA Λ S _ _ _ _ _ _ _ _ _ _ μ _ j hj K₀ K₁ K₂ hT hdense D₀ D₁ D₂ hD₀ hD₁ hD₂ hfin h01
    w hwm hwi hw2 hw0
  set B := K₀ ⊓ K₁ ⊓ K₂ with hBdef
  have hBE1 : B ≤ K₀ ⊓ K₁ := inf_le_left
  have hBE2 : B ≤ K₀ ⊓ K₂ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hBE3 : B ≤ K₁ ⊓ K₂ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hE1K0 : K₀ ⊓ K₁ ≤ K₀ := inf_le_left
  have hE1K1 : K₀ ⊓ K₁ ≤ K₁ := inf_le_right
  have hE2K0 : K₀ ⊓ K₂ ≤ K₀ := inf_le_left
  have hE2K2 : K₀ ⊓ K₂ ≤ K₂ := inf_le_right
  have hE3K1 : K₁ ⊓ K₂ ≤ K₁ := inf_le_left
  have hE3K2 : K₁ ⊓ K₂ ≤ K₂ := inf_le_right
  have hBK0 : B ≤ K₀ := hBE1.trans hE1K0
  have hBK1 : B ≤ K₁ := hBE1.trans hE1K1
  have i0 : (B.subgroupOf K₀).index ≠ 0 := hT.fin₀
  have i1 : (B.subgroupOf K₁).index ≠ 0 := hT.fin₁
  have i2 : (B.subgroupOf K₂).index ≠ 0 := hT.fin₂
  have iBE1 := (idx_ne hBE1 hE1K0 i0).1
  have iE1K0 := (idx_ne hBE1 hE1K0 i0).2
  have iE1K1 := (idx_ne hBE1 hE1K1 i1).2
  have iBE2 := (idx_ne hBE2 hE2K0 i0).1
  have iE2K0 := (idx_ne hBE2 hE2K0 i0).2
  have iBE3 := (idx_ne hBE3 hE3K1 i1).1
  have iE3K1 := (idx_ne hBE3 hE3K1 i1).2
  obtain ⟨DB, hDB⟩ := u_dom μ hU hj hBK0 i0 hD₀
  obtain ⟨DE1, hDE1⟩ := u_dom μ hU hj hE1K0 iE1K0 hD₀
  obtain ⟨DE2, hDE2⟩ := u_dom μ hU hj hE2K0 iE2K0 hD₀
  obtain ⟨DE3, hDE3⟩ := u_dom μ hU hj hE3K1 iE3K1 hD₁

  have hm0 := u_measure μ hU hj hBK0 i0 hD₀ hDB
  have hm1 := u_measure μ hU hj hBK1 i1 hD₁ hDB
  have : Countable (K₀.map j) := countable_map
  have hD0ne : μ D₀ ≠ 0 := hD₀.measure_ne_zero (NeZero.ne μ)
  have hidx : (B.subgroupOf K₀).index = (B.subgroupOf K₁).index := by
    have h : ((B.subgroupOf K₀).index : ENNReal) * μ D₀ = (B.subgroupOf K₁).index * μ D₀ := by
      rw [← hm0, hm1, h01]
    exact_mod_cast (ENNReal.mul_left_inj hD0ne hfin.ne).1 h
  have hDBfin : μ DB < ⊤ := by
    rw [hm0]; exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin
  have : IsFiniteMeasure (μ.restrict DB) := isFiniteMeasure_restrict.2 hDBfin.ne
  have : IsFiniteMeasure (μ.restrict D₁) := isFiniteMeasure_restrict.2 (h01 ▸ hfin).ne

  have hwB : LInv j B w := linv_mono j hBK1 hwi
  have hw2B : IntegrableOn (fun x => w x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBK1 i1 hD₁ hDB (hwm.pow_const 2) (linv_sq j hwi)).2 hw2
  have hwG : Good j B μ DB w := (good_iff hwm hwB).2 hw2B

  set v := avg j (K₀ ⊓ K₁) K₀ w with hv
  have hvm : Measurable v := u_meas μ hU hj hE1K0 iE1K0 hwm
  have hvK : LInv j K₀ v := u_inv μ hU hj hE1K0 iE1K0 (linv_mono j hE1K1 hwi)
  have hv2 : IntegrableOn (fun x => v x ^ 2) D₀ μ := by
    have h1 : IntegrableOn (fun x => w x ^ 2) DE1 μ :=
      (int_iff_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 (hwm.pow_const 2) (linv_sq j hwi)).2 hw2
    rw [u_int_iff μ hU hj hE1K0 iE1K0 hD₀ hDE1 (hwm.pow_const 2)
      (linv_sq j (linv_mono j hE1K1 hwi))] at h1
    have e : (avg j (K₀ ⊓ K₁) K₀ fun y => |w y ^ 2|) = avg j (K₀ ⊓ K₁) K₀ fun y => w y ^ 2 := by
      congr 1; funext y; exact abs_of_nonneg (sq_nonneg _)
    rw [e] at h1
    refine h1.mono' (hvm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact avg_sq_le j iE1K0 w x
  have hv2B : IntegrableOn (fun x => v x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBK0 i0 hD₀ hDB (hvm.pow_const 2) (linv_sq j hvK)).2 hv2
  have hvG : Good j B μ DB v := (good_iff hvm (linv_mono j hBK0 hvK)).2 hv2B

  have hwint1 : IntegrableOn w D₁ μ :=
    ((memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).2 hw2).integrable (by norm_num)
  have hwE1 : IntegrableOn w DE1 μ := (int_iff_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 hwm hwi).2 hwint1
  have hv0 : ∫ x in D₀, v x ∂μ = 0 := by
    have e1 := int_eq_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 hwm hwi hwE1
    have e2 := u_int_eq μ hU hj hE1K0 iE1K0 hD₀ hDE1 hwm (linv_mono j hE1K1 hwi) hwE1
    rw [hw0, mul_zero] at e1
    rw [e1] at e2
    have hne : (((K₀ ⊓ K₁).subgroupOf K₀).index : ℝ) ≠ 0 := by exact_mod_cast iE1K0
    exact (mul_eq_zero.1 e2.symm).resolve_left hne

  have hker : cls j B μ DB v ∈
      (W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₀ ⊓ K₂) ⊓ W j B μ DB (K₁ ⊓ K₂))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro f hf
    obtain ⟨F, hF, rfl⟩ := cls_surj f
    rw [Submodule.mem_inf, Submodule.mem_inf] at hf
    obtain ⟨⟨h1, h2⟩, h3⟩ := hf
    have inv : ∀ {E : Subgroup Λ}, B ≤ E → (B.subgroupOf E).index ≠ 0 → ∀ {DE : Set S},
        IsFundamentalDomain (E.map j) DE μ → cls j B μ DB F ∈ W j B μ DB E →
        ∀ γ ∈ E, (fun x => F (j γ * x)) =ᵐ[μ] F := by
      intro E hBE hiE DE hDE hW γ hγ
      have hae := ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE hiE hDE hF hW
      have hG := good_avg hU hj hDB hBE hiE hDE hF
      have hsp := ae_spread hDB hF.1 hG.1 hF.2.1 hG.2.1 hae
      have hinv := u_inv μ hU hj hBE hiE hF.2.1
      have e : (fun x => avg j B E F (j γ * x)) = avg j B E F := funext fun x => hinv γ hγ x
      exact ((ae_translate (j γ) hsp).trans (Filter.EventuallyEq.of_eq e)).trans hsp.symm
    let G : Subgroup Λ :=
      { carrier := {γ | (fun x => F (j γ * x)) =ᵐ[μ] F}
        one_mem' := by
          simp only [Set.mem_ofPred_eq, map_one, one_mul]; exact Filter.EventuallyEq.rfl
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq, map_mul, mul_assoc] at ha hb ⊢
          exact (ae_translate (j b) ha).trans hb
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
          have := ae_translate (j a)⁻¹ ha
          simp only [mul_inv_cancel_left] at this
          exact this.symm }
    have hE1G : K₀ ⊓ K₁ ≤ G := fun γ hγ => inv hBE1 iBE1 hDE1 h1 γ hγ
    have hE2G : K₀ ⊓ K₂ ≤ G := fun γ hγ => inv hBE2 iBE2 hDE2 h2 γ hγ
    have hE3G : K₁ ⊓ K₂ ≤ G := fun γ hγ => inv hBE3 iBE3 hDE3 h3 γ hγ
    obtain ⟨g, hg, hgB⟩ := exists_not_mem hT.big₀₂
    have hgE1 : g ∉ K₀ ⊓ K₁ := fun h => hgB (Subgroup.mem_inf.2 ⟨h, (Subgroup.mem_inf.1 hg).2⟩)
    have hK0 : K₀ ≤ G := twoTr_le hT.two₀ hE1G (Subgroup.mem_inf.1 hg).1 hgE1 (hE2G hg)
    obtain ⟨g', hg', hg'B⟩ := exists_not_mem hT.big₀₁
    have hg'E3 : g' ∉ K₁ ⊓ K₂ := fun h =>
      hg'B (Subgroup.mem_inf.2 ⟨hg', (Subgroup.mem_inf.1 h).2⟩)
    have hK1 : K₁ ≤ G := twoTr_le hT.two₁ hE3G (Subgroup.mem_inf.1 hg').2 hg'E3 (hE1G hg')
    have hsup : K₀ ⊔ K₁ ≤ G := sup_le hK0 hK1
    obtain ⟨c, hc⟩ := hA S μ ((K₀ ⊔ K₁).map j) hdense F hF.1 (by
      rintro _ ⟨γ, hγ, rfl⟩
      exact hsup hγ)
    rw [cls_inner hF hvG]
    have hFc : (fun x => F x * v x) =ᵐ[μ.restrict DB] fun x => c * v x :=
      (ae_restrict_of_ae hc).mono fun x hx => by dsimp only; rw [hx]
    have hvint : IntegrableOn v DB μ := hvG.2.2.integrable (by norm_num)
    rw [integral_congr_ae hFc, integral_const_mul,
      int_eq_inv μ hU hj hBK0 i0 hD₀ hDB hvm hvK hvint, hv0, mul_zero, mul_zero]

  have hB1 : B = (K₀ ⊓ K₁) ⊓ (K₀ ⊓ K₂) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have hB2 : B = (K₁ ⊓ K₂) ⊓ (K₀ ⊓ K₁) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have hB3 : B = (K₁ ⊓ K₂) ⊓ (K₀ ⊓ K₂) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have a1 := angle hU hj hDB hD hB1 hE1K0 hE2K0 i0 hT.two₀ hT.big₀₂ hD₀ hDE1 hDE2
  have a2 := angle hU hj hDB hD hB2 hE3K1 hE1K1 i1 hT.two₁ hT.big₀₁ hD₁ hDE3 hDE1
  have a3 := angle hU hj hDB hD hB3 hE3K2 hE2K2 i2 hT.two₂ hT.big₀₂ hD₂ hDE3 hDE2
  have le12 := le_inf (W_anti hU hj hDB hBE1 hE1K0 i0 hDE1 hD₀) (W_anti hU hj hDB hBE2 hE2K0 i0 hDE2 hD₀)
  have le13 := le_inf (W_anti hU hj hDB hBE1 hE1K1 i1 hDE1 hD₁) (W_anti hU hj hDB hBE3 hE3K1 i1 hDE3 hD₁)
  have le23 := le_inf (W_anti hU hj hDB hBE2 hE2K2 i2 hDE2 hD₂) (W_anti hU hj hDB hBE3 hE3K2 i2 hDE3 hD₂)
  have hvmem : cls j B μ DB v ∈ W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₀ ⊓ K₂) :=
    Submodule.mem_inf.2 ⟨mem_W_of_inv hU hj hDB hBE1 iBE1 hDE1 hvG (linv_mono j hE1K0 hvK),
      mem_W_of_inv hU hj hDB hBE2 iBE2 hDE2 hvG (linv_mono j hE2K0 hvK)⟩
  have hwmem : cls j B μ DB w ∈ W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₁ ⊓ K₂) :=
    Submodule.mem_inf.2 ⟨mem_W_of_inv hU hj hDB hBE1 iBE1 hDE1 hwG (linv_mono j hE1K1 hwi),
      mem_W_of_inv hU hj hDB hBE3 iBE3 hDE3 hwG (linv_mono j hE3K1 hwi)⟩
  have hmain := hH (HL j B μ DB) (W j B μ DB (K₀ ⊓ K₁)) (W j B μ DB (K₀ ⊓ K₂))
    (W j B μ DB (K₁ ⊓ K₂)) (W j B μ DB K₀) (W j B μ DB K₁) (W j B μ DB K₂)
    (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) (W_closed _ _ _ _ _)
    (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) le12 le13 le23 a1 a2 a3 _ hvmem hker _ hwmem

  have hBw : avg j B K₀ w = v := by
    rw [← u_trans μ hU hj hBK0 i0 hBE1 hE1K0 hwB,
      u_id μ hU hj hBE1 iBE1 (linv_mono j hE1K1 hwi)]
  have hin : ⟪cls j B μ DB v, cls j B μ DB w⟫_ℝ =
      (B.subgroupOf K₀).index * ∫ x in D₀, v x ^ 2 ∂μ := by
    rw [cls_inner hvG hwG, u_int_eq μ hU hj hBK0 i0 hD₀ hDB (u := fun x => v x * w x) (hvm.mul hwm)
      (linv_mul j (linv_mono j hBK0 hvK) hwB) (integrableOn_mul hvG.2.2 hwG.2.2)]
    congr 2; funext x
    rw [avg_mul_left j hvK, hBw, sq]
  have hnv : ‖cls j B μ DB v‖ ^ 2 = (B.subgroupOf K₀).index * ∫ x in D₀, v x ^ 2 ∂μ := by
    rw [cls_norm_sq hvG, int_eq_inv μ hU hj hBK0 i0 hD₀ hDB (u := fun x => v x ^ 2) (hvm.pow_const 2)
      (linv_sq j hvK) hv2B]
  have hnw : ‖cls j B μ DB w‖ ^ 2 = (B.subgroupOf K₀).index * ∫ x in D₁, w x ^ 2 ∂μ := by
    rw [cls_norm_sq hwG, int_eq_inv μ hU hj hBK1 i1 hD₁ hDB (u := fun x => w x ^ 2) (hwm.pow_const 2)
      (linv_sq j hwi) hw2B, hidx]
  refine ⟨hv2, hv0, ?_⟩
  set n : ℝ := ((B.subgroupOf K₀).index : ℝ)
  have hn0 : 0 < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero i0)
  set P := ∫ x in D₀, v x ^ 2 ∂μ
  set Q := ∫ x in D₁, w x ^ 2 ∂μ
  set a := ‖cls j B μ DB v‖
  set b := ‖cls j B μ DB w‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  rw [hin] at hmain
  have h1 : a ^ 2 ≤ 2 / 5 * (a * b) := by rw [hnv]; exact (le_abs_self _).trans hmain
  have h2 : a ^ 2 ≤ (2 / 5) ^ 2 * b ^ 2 := by
    rcases ha.lt_or_eq with ha' | ha'
    · have : a ≤ 2 / 5 * b := by nlinarith
      nlinarith
    · rw [← ha']; nlinarith [sq_nonneg b]
  rw [hnv, hnw] at h2
  have : n * P ≤ n * ((2 / 5) ^ 2 * Q) := by linarith
  exact le_of_mul_le_mul_left this hn0

end PositivityTheory.KB.SpectralGap

end
