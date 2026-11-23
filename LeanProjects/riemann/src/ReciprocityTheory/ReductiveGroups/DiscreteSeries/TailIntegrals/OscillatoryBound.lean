import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExponentConditionNeg
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoMulStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoSqNonneg

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

lemma fS_scl {p m : ℕ} (s : Fin (p + 2) → ℝ) (hs0 : ∀ l, 0 ≤ s l) (τ : ℝ) (hτ : τ ∈ Icc (1 : ℝ) 2)
    (x : Xp (p + 1) m) : fS s (scl τ x) ≤ ENNReal.ofReal (2 ^ ∑ l, s l) * fS s x := by
  unfold fS
  rw [Real.rpow_sum_of_pos (by norm_num), ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro l _
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := de_scl τ hτ.1 hτ.2 x l
  have h2 := de_ge_one x l
  calc de (scl τ x) l ^ (-s l) ≤ (de x l / 2) ^ (-s l) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith [hs0 l])
    _ = 2 ^ s l * de x l ^ (-s l) := by
        rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          div_inv_eq_mul, mul_comm]

lemma fS_rot {p m : ℕ} (s : Fin (p + 2) → ℝ) (t : ℝ) (x : Xp (p + 1) m) : fS s (rot t x) = fS s x := by
  unfold fS
  simp only [de_rot]

end OSAux

open OSAux in
theorem oscillatoryBound' (hT : TailFin) (hC1 : C1) (hS : SUB) (hK : KER) (hL : SLOW) : OS := by
  intro p m δ γ e hδ0 hδ1 hγ0 hγ hepos hsum
  set s : Fin (p + 2) → ℝ := fun l => s0N (p + 1) m l - e l with hs
  have hS0 : 0 ≤ ∑ i : Fin (p + 1), e i.succ := Finset.sum_nonneg (fun i _ => (hepos _).le)
  have hs0 : ∀ l, 0 ≤ s l := by
    intro l
    have hle : e l ≤ 1 := by
      refine Fin.cases ?_ (fun i => ?_) l
      · linarith [hepos 0]
      · have : e i.succ ≤ ∑ i : Fin (p + 1), e i.succ := Finset.single_le_sum
          (f := fun i : Fin (p + 1) => e i.succ) (fun j _ => (hepos _).le) (Finset.mem_univ i)
        linarith [hepos 0]
    have h1 : 1 ≤ s0N (p + 1) m l := by
      unfold s0N; split_ifs
      · norm_num
      · have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith
    simp only [hs]; linarith
  obtain ⟨Cr, hCr0, hrot⟩ := rot_weight hS hδ0 hδ1
  obtain ⟨C2, hC20, hscl⟩ := scl_weight hS hδ0 hδ1 hγ0 hγ
  obtain ⟨C3, hC3⟩ := tail_bound hT hC1 hK hL (m := m) e hγ0 (by linarith) hepos hsum
  set Ks : ℝ := 2 ^ ∑ l, s l with hKs
  have hKs0 : 0 ≤ Ks := by positivity
  refine ⟨Cr * Ks * C2 * max C3 0, ?_⟩
  intro η η' ζ c₀ hη
  set w0 : Xp (p + 1) m → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))
    with hw0d
  set w1 : Xp (p + 1) m → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 + ‖linF η η' ζ x‖) ^ (-δ / 4)) with hw1d
  have hw0 : Measurable w0 :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable (fun r : ℂ => (1 + |2 * r.im + c₀|) ^ (-δ))).comp
      (cont_linF η η' ζ).measurable)
  have hw1 : Measurable w1 :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable (fun r : ℂ => (1 + ‖r‖) ^ (-δ / 4))).comp
      (cont_linF η η' ζ).measurable)
  have hf := meas_fS (p := p) (m := m) s
  have hN : (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) = ENNReal.ofReal (‖η' 0‖ ^ (-γ)) := by
    have e0 : ENNReal.ofReal ‖η' 0‖ = (‖η' 0‖₊ : ℝ≥0∞) := by
      rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
    rw [← e0, ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hη)]
  have stepA : OSInt p m s δ η η' ζ c₀ ≤
      ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4)) * ∫⁻ x, fS s x * w1 x := by
    have hA := avg (μ := volume) rot rot_meas (fun t _ => rot_mp t) hf hw0 1
      (fun t _ x => by rw [one_mul, fS_rot])
    calc OSInt p m s δ η η' ζ c₀ = ∫⁻ x, fS s x * w0 x := rfl
      _ ≤ 1 * ∫⁻ x, fS s x * (∫⁻ t in Icc (1 : ℝ) 2, w0 (rot t x)) := hA
      _ ≤ ∫⁻ x, fS s x * ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖linF η η' ζ x‖) ^ (-δ / 4)) := by
          rw [one_mul]
          refine lintegral_mono (fun x => ?_)
          gcongr
          simp only [hw0d, linF_rot]
          exact hrot _ _
      _ = ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4)) * ∫⁻ x, fS s x * w1 x := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr (fun x => ?_)
          rw [hw1d, ENNReal.ofReal_mul (mul_nonneg hCr0.le (by positivity))]
          ring
  have stepB : ∫⁻ x, fS s x * w1 x ≤
      ENNReal.ofReal Ks * (ENNReal.ofReal C2 * ENNReal.ofReal (‖η' 0‖ ^ (-γ)) *
        ∫⁻ x : Xp (p + 1) m, fS s x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ)) := by
    have hB := avg (μ := volume) scl scl_meas (fun τ hτ => scl_mp τ (by linarith [hτ.1])) hf hw1
      (ENNReal.ofReal Ks) (fun τ hτ x => fS_scl s hs0 τ hτ x)
    refine hB.trans ?_
    gcongr
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_mono (fun x => ?_)
    calc fS s x * (∫⁻ τ in Icc (1 : ℝ) 2, w1 (scl τ x))
        ≤ fS s x * (ENNReal.ofReal C2 * (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ)) := by
          gcongr
          exact hscl η η' ζ x
      _ = _ := by rw [hN]; ring
  have hC3' : ∫⁻ x : Xp (p + 1) m, fS s x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤ ENNReal.ofReal (max C3 0) :=
    hC3.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc OSInt p m s δ η η' ζ c₀
      ≤ ENNReal.ofReal (Cr * (1 + |c₀|) ^ (-δ / 4)) * (ENNReal.ofReal Ks * (ENNReal.ofReal C2 *
          ENNReal.ofReal (‖η' 0‖ ^ (-γ)) * ENNReal.ofReal (max C3 0))) := by
        refine stepA.trans ?_
        gcongr
        exact stepB.trans (by gcongr)
    _ = ENNReal.ofReal (Cr * Ks * C2 * max C3 0 * ‖η' 0‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
        have h1 : 0 ≤ (1 + |c₀|) ^ (-δ / 4) := by positivity
        have h2 : 0 ≤ ‖η' 0‖ ^ (-γ) := by positivity
        have h3 : 0 ≤ max C3 0 := le_max_right _ _
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCr0.le hKs0) hC20.le) h3) h2),
          ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hCr0.le hKs0) hC20.le) h3),
          ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCr0.le hKs0) hC20.le),
          ENNReal.ofReal_mul (mul_nonneg hCr0.le hKs0), ENNReal.ofReal_mul hCr0.le,
          ENNReal.ofReal_mul hCr0.le]
        ring

end ReciprocityTheory.ChartRestriction.DS.Xi
