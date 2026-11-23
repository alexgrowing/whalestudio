import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPolyMaxLowerBound
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax
  limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.Regular

noncomputable section

def regularisedAt {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    (R : RegChartData A) (ρ : Mollifier D) (η : Fin R.N → X → ℝ) (κ E t : ℝ) : X → ℝ :=
  R.regularised ρ (κ * Real.log (Real.log t⁻¹)) t
    (E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹ + t)) η

def RegularisedMonotone.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (η : Fin R.N → X → ℝ) (Cη κ E : ℝ),
    R.IsCutoffFamily η Cη → 0 ≤ κ → 0 ≤ E →
    ∃ C ℓ₀ : ℝ, ∀ t t₀ : ℝ, 0 < t → t ≤ t₀ → ℓ₀ ≤ Real.log t₀⁻¹ → ∀ x : X,
      regularisedAt R ρ η κ E t x ≤
        regularisedAt R ρ η κ E t₀ x + C * (Real.log (Real.log t₀⁻¹) / Real.log t₀⁻¹)

theorem regularisedMonotone_hyp : CompactSpace Unit ∧ T2Space Unit ∧ Nonempty (Mollifier 0) ∧
    pointReg.IsCutoffFamily (fun _ _ => 0) 1 :=
  ⟨inferInstance, inferInstance, ReciprocityTheory.AnForm.A.mollifierInhabit_thm 0, pointCutoff⟩

theorem le_logLog_div {t ℓ : ℝ} (ht : 0 < t) (hℓdef : ℓ = Real.log t⁻¹) (hℓe : Real.exp 1 ≤ ℓ) :
    t ≤ Real.log ℓ / ℓ := by
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlog1 : 1 ≤ Real.log ℓ := by rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  have hlogt : Real.log t = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have htexp : t = Real.exp (-ℓ) := by rw [← hlogt, Real.exp_log ht]
  rw [htexp, Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos ℓ)]
  have h5 : ℓ + 1 ≤ Real.exp ℓ := Real.add_one_le_exp ℓ
  have h6 : 1 ≤ Real.exp ℓ * (Real.log ℓ / ℓ) := by
    rw [mul_div_assoc', le_div_iff₀ hℓ0, one_mul]
    have := le_mul_of_one_le_right (Real.exp_pos ℓ).le hlog1
    linarith
  rw [mul_comm]; exact h6

theorem RegularisedMonotone.proof : RegularisedMonotone.Statement := by
  intro X _ _ _ D A R ρ η Cη κ E hη hκ hE
  obtain ⟨δ, B₀, hδ, hV⟩ := TruncPsh.proof X D A R
  choose V hVo hVt hVball hVpsh using hV
  obtain ⟨C₂, t₂, ht₂, hlow⟩ := PolyMaxLowerBound.proof X D A R
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨B', hB'⟩ : ∃ c : ℝ, c = max B₀ 0 := ⟨_, rfl⟩
  obtain ⟨C₂', hC₂'⟩ : ∃ c : ℝ, c = max C₂ 0 := ⟨_, rfl⟩
  have hB'0 : 0 ≤ B' := hB' ▸ le_max_right _ _
  have hB₀B' : B₀ ≤ B' := hB' ▸ le_max_left _ _
  have hC₂'0 : 0 ≤ C₂' := hC₂' ▸ le_max_right _ _
  have hC₂C₂' : C₂ ≤ C₂' := hC₂' ▸ le_max_left _ _
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / 2)| := ⟨_, rfl⟩
  have hL16 : 0 ≤ Real.log (4 * 2 ^ 2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨E₁, hE₁⟩ : ∃ c : ℝ, c = 2 * Real.log (4 * 2 ^ 2 : ℝ) * (B' + C₂') := ⟨_, rfl⟩
  have hE₁0 : 0 ≤ E₁ := by rw [hE₁]; positivity
  refine ⟨10 * E + c₀ * E₁,
    max (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2))) + 1,
    fun t t₀ ht htt₀ hℓ x => ?_⟩
  have ht₀ : 0 < t₀ := ht.trans_le htt₀
  obtain ⟨ℓ, hℓdef⟩ : ∃ s : ℝ, s = Real.log t₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨ℓt, hℓtdef⟩ : ∃ s : ℝ, s = Real.log t⁻¹ := ⟨_, rfl⟩
  rw [← hℓdef] at hℓ
  have h1 := le_max_left (Real.exp 1) (2 * a)
  have h2 := le_max_right (Real.exp 1) (2 * a)
  have h3 := le_max_left (-Real.log t₂) (-Real.log (δ / 2))
  have h4 := le_max_right (-Real.log t₂) (-Real.log (δ / 2))
  have h5 := le_max_left (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2)))
  have h6 := le_max_right (max (Real.exp 1) (2 * a)) (max (-Real.log t₂) (-Real.log (δ / 2)))
  have hℓe : Real.exp 1 ≤ ℓ := by linarith
  have hℓa : 2 * a ≤ ℓ := by linarith
  have hlogt₀ : Real.log t₀ = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have htt₂ : t₀ < t₂ := (Real.log_lt_log_iff ht₀ ht₂).1 (by linarith)
  have htδ : t₀ < δ / 2 := (Real.log_lt_log_iff ht₀ (by linarith)).1 (by linarith)
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlog1 : 1 ≤ Real.log ℓ := by rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  obtain ⟨q, hqdef⟩ : ∃ s : ℝ, s = Real.log ℓ / ℓ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; exact div_nonneg (by linarith) hℓ0.le
  have htq : t₀ ≤ q := hqdef ▸ le_logLog_div ht₀ hℓdef hℓe
  have hqℓ : q * ℓ = Real.log ℓ := by rw [hqdef]; field_simp

  have hℓℓt : ℓ ≤ ℓt := by
    rw [hℓdef, hℓtdef]; exact Real.log_le_log (inv_pos.2 ht₀) (inv_anti₀ ht htt₀)
  have hqt : Real.log ℓt / ℓt ≤ q := by
    have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hℓℓt))
      hℓℓt
    simp only at h
    rw [hqdef]; exact h
  have hlogℓt : Real.log ℓ ≤ Real.log ℓt := Real.log_le_log hℓ0 hℓℓt
  have hKK : κ * Real.log ℓ ≤ κ * Real.log ℓt := mul_le_mul_of_nonneg_left hlogℓt hκ
  have hK0 : 0 ≤ κ * Real.log ℓ := mul_nonneg hκ (by linarith)
  have hqt0 : 0 ≤ Real.log ℓt / ℓt := div_nonneg (by linarith) (by linarith)
  have hεt0 : 0 ≤ E * (Real.log ℓt / ℓt + t) := mul_nonneg hE (by linarith)
  have hε0 : 0 ≤ E * (q + t₀) := mul_nonneg hE (by linarith)
  have hεle : E * (Real.log ℓt / ℓt + t) ≤ E * (q + t₀) :=
    mul_le_mul_of_nonneg_left (by linarith) hE
  have hε2 : E * (q + t₀) ≤ 2 * E * q := by
    have := mul_le_mul_of_nonneg_left htq hE
    linarith

  have key : ∀ j, x ∈ R.mid j → R.phReg ρ (κ * Real.log ℓt) t j x ≤
      R.phReg ρ (κ * Real.log ℓ) t₀ j x + c₀ * E₁ * q := by
    intro j hx
    obtain ⟨hp₀, hbd₀⟩ := hVpsh j (κ * Real.log ℓ)
    have hball : ∀ s, s ≤ δ → closedBall (R.chart j x) s ⊆ V j := fun s hs =>
      (closedBall_subset_closedBall hs).trans (hVball j x hx)
    have h2t : 2 * t₀ ≤ δ := by linarith

    have hpt := (hVpsh j (κ * Real.log ℓt)).1
    have hi : molli ρ t (R.trunc (κ * Real.log ℓt) j) (R.chart j x) ≤
        polyMax (R.trunc (κ * Real.log ℓt) j) (R.chart j x) t :=
      (((mollify_thm D ρ (V j) _ (hVo j) hpt).1 t ht).2.2.2 (R.chart j x)
        (hball t (by linarith))).2
    have hii : polyMax (R.trunc (κ * Real.log ℓt) j) (R.chart j x) t ≤
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) := by
      refine polyMax_le' ht.le fun y hy => ?_
      have hyV : y ∈ V j := hball t (by linarith) hy
      exact TruncTransfer.limsupExt_max_le (R.chart j).open_target (R.S j) (R.u j) _ _ t₀
        (hVt j hyV) ht₀ fun y' hy' _ hy'S => by
          have hy'b : y' ∈ closedBall (R.chart j x) (2 * t₀) := by
            rw [mem_closedBall]; rw [mem_ball] at hy'; rw [mem_closedBall] at hy
            linarith [dist_triangle y' y (R.chart j x)]
          have e : R.trunc (κ * Real.log ℓ) j y' = max (R.u j y') (-(κ * Real.log ℓ)) := by
            simp only [RegChartData.trunc, limsupExt, if_neg hy'S]
          calc max (R.u j y') (-(κ * Real.log ℓt)) ≤ max (R.u j y') (-(κ * Real.log ℓ)) :=
                max_le_max le_rfl (neg_le_neg hKK)
            _ = R.trunc (κ * Real.log ℓ) j y' := e.symm
            _ ≤ _ := le_polyMax hp₀.1 (hball _ h2t) hy'b

    have hiv := MollifiedLowerBound.full D ρ b (V j) (R.trunc (κ * Real.log ℓ) j) (R.chart j x) t₀
      (hVo j) hp₀ ht₀ (hball _ h2t) hb
    rw [← hc₀] at hiv
    have hv := PolyMaxOscillation.full D (V j) (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ t₀ 2
      (hVo j) hp₀ (hball δ le_rfl) ht₀ (by norm_num) (by linarith)
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) s ≤
          polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hp₀.1 hs hss' (hball _ hs')
    have e1 := mono (t₀ / (4 * 2)) (t₀ / 4) (by linarith) (by linarith) (by linarith)
    have e2 := mono t₀ (2 * t₀) ht₀.le (by linarith) h2t
    have hlowj := hlow t₀ ht₀ htt₂ (κ * Real.log ℓ) j x hx
    rw [← hℓdef] at hlowj
    have hMδ : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ ≤ B' :=
      polyMax_le' hδ.le fun y hy => (hbd₀ y (hVball j x hx hy)).trans
        (max_le hB₀B' (by linarith))
    have hN : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) ≤ (B' + C₂') * Real.log ℓ := by
      have h1' : C₂ * Real.log ℓ ≤ C₂' * Real.log ℓ :=
        mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
      have h2' : B' ≤ B' * Real.log ℓ := le_mul_of_one_le_right hB'0 hlog1
      linarith
    have hden : ℓ / 2 ≤ Real.log (δ / (2 * t₀)) := by
      rw [show δ / (2 * t₀) = (δ / 2) * t₀⁻¹ by field_simp,
        Real.log_mul (by linarith : (0 : ℝ) < δ / 2).ne' (inv_pos.2 ht₀).ne']
      have := neg_abs_le (Real.log (δ / 2))
      rw [← ha] at this
      linarith
    have hden0 : 0 < Real.log (δ / (2 * t₀)) := by linarith
    have hO : polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (t₀ / (4 * 2)) ≤ E₁ * q := by
      refine hv.trans ?_
      rw [div_le_iff₀ hden0]
      calc Real.log (4 * 2 ^ 2) * (polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) δ -
              polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀))
          ≤ Real.log (4 * 2 ^ 2) * ((B' + C₂') * Real.log ℓ) :=
            mul_le_mul_of_nonneg_left hN hL16
        _ = E₁ * q * (ℓ / 2) := by rw [hE₁, ← hqℓ]; ring
        _ ≤ E₁ * q * Real.log (δ / (2 * t₀)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg hE₁0 hq0)
    have hc : c₀ * (polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (2 * t₀) -
        polyMax (R.trunc (κ * Real.log ℓ) j) (R.chart j x) (t₀ / 4)) ≤ c₀ * (E₁ * q) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    simp only [RegChartData.phReg, RegChartData.smoothed]
    linarith

  have hg := LogLogRegularisation.glue_le R.toPotentialCharts
    (fun j x => R.phReg ρ (κ * Real.log ℓt) t j x + 4 * (E * (Real.log ℓt / ℓt + t)) * η j x)
    hεt0 (c := regularisedAt R ρ η κ E t₀ x + 4 * (E * (q + t₀)) + c₀ * E₁ * q) (x := x)
    fun j hx => by
      have hb' := hη.bounds j x hx
      have hlo := LogLogRegularisation.le_glue R.toPotentialCharts
        (fun j x => R.phReg ρ (κ * Real.log ℓ) t₀ j x + 4 * (E * (q + t₀)) * η j x) hε0 hx
      have e : R.toPotentialCharts.glue
          (fun j x => R.phReg ρ (κ * Real.log ℓ) t₀ j x + 4 * (E * (q + t₀)) * η j x)
          (E * (q + t₀)) x = regularisedAt R ρ η κ E t₀ x := by
        simp only [regularisedAt, ← hℓdef, ← hqdef]; rfl
      rw [e] at hlo
      have hk := key j hx
      have m1 : 4 * (E * (Real.log ℓt / ℓt + t)) * η j x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hb'.2
      have m2 : 0 ≤ 4 * (E * (q + t₀)) * (η j x + 1) := mul_nonneg (by linarith) (by linarith)
      linarith
  have e : R.toPotentialCharts.glue
      (fun j x => R.phReg ρ (κ * Real.log ℓt) t j x + 4 * (E * (Real.log ℓt / ℓt + t)) * η j x)
      (E * (Real.log ℓt / ℓt + t)) x = regularisedAt R ρ η κ E t x := by
    simp only [regularisedAt, ← hℓtdef]; rfl
  rw [e] at hg
  rw [← hℓdef, ← hqdef]
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
