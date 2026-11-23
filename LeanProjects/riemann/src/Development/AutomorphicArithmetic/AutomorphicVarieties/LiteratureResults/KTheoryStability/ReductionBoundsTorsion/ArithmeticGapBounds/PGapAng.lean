import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AeEqCosetAvgOfMemInvariantSubspace

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap.PGap

theorem pt_bound {z p q t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 < t) (h : z ^ 2 ≤ 1 / 25 * (p * q)) :
    |z| ≤ (t * p + q / t) / 10 := by
  have hts : t * (q / t) = q := by field_simp
  have hw : 0 ≤ (t * p + q / t) / 10 := by positivity
  have h4 : z ^ 2 ≤ ((t * p + q / t) / 10) ^ 2 := by
    nlinarith [sq_nonneg (t * p - q / t)]
  exact abs_le_of_sq_le_sq' h4 hw |> fun h => abs_le.mpr h

section Ang

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  {μ : Measure S} [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B : Subgroup Λ} {DB : Set S}
  (hDB : IsFundamentalDomain (B.map j) DB μ)

include hU hj hDB

theorem perp_avg {K : Subgroup Λ} (hBK : B ≤ K) (hiK : (B.subgroupOf K).index ≠ 0) {DK : Set S}
    (hDK : IsFundamentalDomain (K.map j) DK μ) {a : S → ℝ} (ha : Good j B μ DB a)
    (hperp : cls j B μ DB a ∈ (W j B μ DB K)ᗮ) : cls j B μ DB (avg j B K a) = 0 := by
  have hm := good_avg hU hj hDB hBK hiK hDK ha
  have hmK : LInv j K (avg j B K a) := u_inv μ hU hj hBK hiK ha.2.1
  have hmW := mem_W_of_inv hU hj hDB hBK hiK hDK hm hmK
  have h0 := Submodule.inner_right_of_mem_orthogonal hmW hperp
  rw [cls_inner hm ha] at h0
  have key : ∫ x in DB, avg j B K a x ^ 2 ∂μ = ∫ x in DB, avg j B K a x * a x ∂μ := by
    have e : (fun x => avg j B K a x ^ 2) = fun x => avg j B K a x * avg j B K a x := by
      funext x; ring
    rw [e, u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * avg j B K a x) (hm.1.mul hm.1) (linv_mul j hm.2.1 hm.2.1)
        (integrableOn_mul hm.2.2 hm.2.2),
      u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * a x) (hm.1.mul ha.1) (linv_mul j hm.2.1 ha.2.1)
        (integrableOn_mul hm.2.2 ha.2.2)]
    congr 2; funext x
    rw [avg_mul_left j hmK, avg_mul_left j hmK, u_id μ hU hj hBK hiK hmK]
  have hn : ‖cls j B μ DB (avg j B K a)‖ ^ 2 = 0 := by rw [cls_norm_sq hm, key, h0]
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hn)

theorem core (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ) {a b : S → ℝ} (ha : Good j B μ DB a)
    (haE : LInv j E a) (hz : ∀ x, avg j B K a x = 0) (hb : Good j B μ DB b) (hbE : LInv j E' b) :
    |∫ x in DB, a x * b x ∂μ| ≤
      1 / 5 * (Real.sqrt (∫ x in DB, a x ^ 2 ∂μ) * Real.sqrt (∫ x in DB, b x ^ 2 ∂μ)) := by
  have hBK : B ≤ K := hB ▸ inf_le_left.trans hEK
  have hab := integrableOn_mul ha.2.2 hb.2.2
  have haa := integrableOn_mul ha.2.2 ha.2.2
  have hbb := integrableOn_mul hb.2.2 hb.2.2
  have sa : (fun x => a x ^ 2) = fun x => a x * a x := by funext x; ring
  have sb : (fun x => b x ^ 2) = fun x => b x * b x := by funext x; ring
  rw [sa, sb]
  rw [u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb]
  have iab := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab
  have iaa := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa
  have ibb := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Nat.pos_of_ne_zero hiK
  set I := ∫ x in DK, avg j B K (fun y => a y * b y) x ∂μ
  set X := ∫ x in DK, avg j B K (fun y => a y * a y) x ∂μ
  set Y := ∫ x in DK, avg j B K (fun y => b y * b y) x ∂μ
  have pa : ∀ x, 0 ≤ avg j B K (fun y => a y * a y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have pb : ∀ x, 0 ≤ avg j B K (fun y => b y * b y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have hX : 0 ≤ X := integral_nonneg pa
  have hY : 0 ≤ Y := integral_nonneg pb
  have hpt : ∀ x, avg j B K (fun y => a y * b y) x ^ 2 ≤
      1 / 25 * (avg j B K (fun y => a y * a y) x * avg j B K (fun y => b y * b y) x) := by
    intro x
    have := hD Λ S j B E E' K hB hEK hE'K hiK htwo hbig a b haE hbE x (hz x)
    simpa only [sq] using this
  have ht : ∀ t : ℝ, 0 < t → |I| ≤ (t * X + Y / t) / 10 := by
    intro t ht
    calc |I| ≤ ∫ x in DK, |avg j B K (fun y => a y * b y) x| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.restrict DK)
            (fun x => avg j B K (fun y => a y * b y) x)
      _ ≤ ∫ x in DK, (t * avg j B K (fun y => a y * a y) x + avg j B K (fun y => b y * b y) x / t) / 10 ∂μ :=
          integral_mono iab.abs (((iaa.const_mul t).add (ibb.div_const t)).div_const 10)
            fun x => pt_bound (pa x) (pb x) ht (hpt x)
      _ = (t * X + Y / t) / 10 := by
          rw [integral_div, integral_add (iaa.const_mul t) (ibb.div_const t), integral_const_mul,
            integral_div]
  have h1 := t_trick hX hY ht
  rw [abs_mul, abs_of_pos hn0, Real.sqrt_mul hn0.le, Real.sqrt_mul hn0.le]
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  calc n * |I| ≤ n * (1 / 5 * (Real.sqrt X * Real.sqrt Y)) := mul_le_mul_of_nonneg_left h1 hn0.le
    _ = 1 / 5 * (Real.sqrt n * Real.sqrt X * (Real.sqrt n * Real.sqrt Y)) := by
      linear_combination (-(1 / 5 * (Real.sqrt X * Real.sqrt Y))) * hs

theorem angle (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK DE DE' : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ)
    (hDE : IsFundamentalDomain (E.map j) DE μ) (hDE' : IsFundamentalDomain (E'.map j) DE' μ) :
    ∀ u ∈ W j B μ DB E, u ∈ (W j B μ DB K)ᗮ → ∀ u' ∈ W j B μ DB E',
      |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖) := by
  intro u hu hperp u' hu'
  have hBE : B ≤ E := hB ▸ inf_le_left
  have hBE' : B ≤ E' := hB ▸ inf_le_right
  have hBK : B ≤ K := hBE.trans hEK
  have hiE := (idx_ne hBE hEK hiK).1
  have hiE' := (idx_ne hBE' hE'K hiK).1
  obtain ⟨a, ha, rfl⟩ := cls_surj u
  obtain ⟨b, hb, rfl⟩ := cls_surj u'
  have ha1 := good_avg hU hj hDB hBE hiE hDE ha
  have ha1E : LInv j E (avg j B E a) := u_inv μ hU hj hBE hiE ha.2.1
  have e1 : cls j B μ DB a = cls j B μ DB (avg j B E a) :=
    (cls_eq_iff ha ha1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE hiE hDE ha hu)
  have hb1 := good_avg hU hj hDB hBE' hiE' hDE' hb
  have hb1E : LInv j E' (avg j B E' b) := u_inv μ hU hj hBE' hiE' hb.2.1
  have e2 : cls j B μ DB b = cls j B μ DB (avg j B E' b) :=
    (cls_eq_iff hb hb1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE' hiE' hDE' hb hu')
  rw [e1] at hperp ⊢
  rw [e2]
  have hm := good_avg hU hj hDB hBK hiK hDK ha1
  have hmK : LInv j K (avg j B K (avg j B E a)) := u_inv μ hU hj hBK hiK ha1.2.1
  have h0 := perp_avg hU hj hDB hBK hiK hDK ha1 hperp
  have ha2 := good_sub ha1 hm
  have e3 : cls j B μ DB (avg j B E a) =
      cls j B μ DB (fun x => avg j B E a x - avg j B K (avg j B E a) x) := by
    rw [cls_sub ha1 hm, h0, sub_zero]
  rw [e3]
  have ha2E : LInv j E (fun x => avg j B E a x - avg j B K (avg j B E a) x) :=
    linv_sub j ha1E (linv_mono j hEK hmK)
  have hz : ∀ x, avg j B K (fun x => avg j B E a x - avg j B K (avg j B E a) x) x = 0 := by
    intro x
    rw [avg_sub j hiK, u_id μ hU hj hBK hiK hmK, sub_self]
  rw [cls_inner ha2 hb1, ← Real.sqrt_sq (norm_nonneg (cls j B μ DB _)),
    ← Real.sqrt_sq (norm_nonneg (cls j B μ DB (avg j B E' b))), cls_norm_sq ha2, cls_norm_sq hb1]
  exact core hU hj hDB hD hB hEK hE'K hiK htwo hbig hDK ha2 ha2E hz hb1 hb1E

end Ang

end PositivityTheory.KB.SpectralGap.PGap

end
