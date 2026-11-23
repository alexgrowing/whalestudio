import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding

noncomputable section

namespace GlobalTheory.CompactDualQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def sg {P Q : ℕ} : Fin P ⊕ Fin Q → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

def SignCompat (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Prop :=
  ∀ i, sg (e (some i)) = sg i

def l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : ℝ := ∑ i, ∑ j, ‖Z i j‖

def gauge (g : UpqT P Q) : ℝ := l1 (UpqT.mat g - 1)

def baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Sp P Q := Pi.single (e none) 1

def ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ + 2 * ∑ i, ‖y (e (some i))‖

def tanGauge (t : ℝ × Sp P' Q') : ℝ := |t.1| + 2 * ∑ i, ‖t.2 i‖

def polarPt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim
    ((Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I)) t.2

def IsBlockEmb (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  ∀ g, UpqT.mat (j g) (e none) (e none) = 1 ∧ (∀ b, UpqT.mat (j g) (e none) (e (some b)) = 0) ∧
    (∀ a, UpqT.mat (j g) (e (some a)) (e none) = 0) ∧
    ∀ a b, UpqT.mat (j g) (e (some a)) (e (some b)) = UpqT.mat g a b

def expBall (P Q : ℕ) (r : ℝ) : Set (UpqT P Q) :=
  {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
    NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}

theorem sg_eq (i : Fin P ⊕ Fin Q) : sg i = 1 ∨ sg i = -1 := by
  rcases i with i | i <;> simp [sg]

theorem sg_ne_zero (i : Fin P ⊕ Fin Q) : sg i ≠ 0 := by
  rcases sg_eq i with h | h <;> rw [h] <;> norm_num

theorem qf_eq_sum (x : Sp P Q) : qf x = ∑ i, sg i * Complex.normSq (x i) := by
  simp [qf, sg, Fintype.sum_sum_type, sub_eq_add_neg]

theorem qf_baseVec (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    qf (baseVec e) = sg (e none) := by
  rw [qf_eq_sum, Finset.sum_eq_single (e none)]
  · simp [baseVec]
  · intro b _ hb; simp [baseVec, hb]
  · simp

theorem card_eq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : P + Q = P' + Q' + 1 := by
  simpa using (Fintype.card_congr e).symm

theorem polarPt_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') :
    polarPt e t (e none) =
      (Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I) := by
  simp [polarPt]

theorem polarPt_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : polarPt e t (e (some i)) = t.2 i := by
  simp [polarPt]

theorem weightAbsEntrySum_nonneg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : 0 ≤ l1 Z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_matrixEntryAbsSum : Continuous (l1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → ℝ) :=
  continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm

theorem continuous_gauge : Continuous (gauge : UpqT P Q → ℝ) :=
  continuous_matrixEntryAbsSum.comp
    ((Units.continuous_val.comp continuous_subtype_val : Continuous UpqT.mat).sub continuous_const)

theorem ptGauge_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) :
    0 ≤ ptGauge e y := by
  unfold ptGauge; positivity

theorem continuous_ptGauge (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (ptGauge e) := by
  unfold ptGauge; fun_prop

theorem tanGauge_nonneg (t : ℝ × Sp P' Q') : 0 ≤ tanGauge t := by
  unfold tanGauge; positivity

theorem continuous_tanGauge : Continuous (tanGauge : ℝ × Sp P' Q' → ℝ) := by
  unfold tanGauge; fun_prop

theorem tendsto_div_of_squeeze {F V A : ℝ → ℝ≥0∞} {n : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hV : ∀ t r : ℝ, 0 < t → 0 < r → V (t * r) = ENNReal.ofReal (t ^ n) * V r)
    (hF : Tendsto (fun r => F r / V r) (𝓝[>] 0) (𝓝 c))
    (hA : ∀ t : ℝ, 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), F (t⁻¹ * r) ≤ A r ∧ A r ≤ F (t * r)) :
    Tendsto (fun r => A r / V r) (𝓝[>] 0) (𝓝 c) := by
  have key : ∀ t : ℝ, 0 < t →
      Tendsto (fun r => F (t * r) / V r) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ n) * c)) := by
    intro t ht
    have h1 : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos ht hr
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (t ^ n)) (hF.comp h1)
      (Or.inr ENNReal.ofReal_ne_top)
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have h0 : ENNReal.ofReal (t ^ n) ≠ 0 := by simpa using pow_pos ht n
    simp only [Function.comp, hV t r ht hr]
    rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ h0 ENNReal.ofReal_ne_top]
  have lim : ∀ u : ℝ → ℝ, ContinuousAt u 1 → u 1 = 1 →
      Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n) * c) (𝓝[>] 1) (𝓝 c) := by
    intro u hu h1
    have h3 : Tendsto (fun t : ℝ => ENNReal.ofReal (u t ^ n)) (𝓝 1) (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.continuousAt.comp (hu.pow n)).tendsto
      simp only [Function.comp, Pi.pow_apply, h1, one_pow, ENNReal.ofReal_one] at this
      exact this
    have := ENNReal.Tendsto.mul_const (b := c) h3 (Or.inr hc)
    rw [one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t⁻¹) (continuousAt_inv₀ one_ne_zero) inv_one).eventually
      (lt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t⁻¹ (inv_pos.2 (by linarith))).eventually (lt_mem_nhds h1), hA t ht]
      with r h3 h4 using h3.trans_le (ENNReal.div_le_div_right h4.1 _)
  · obtain ⟨t, h1, h2⟩ := (((lim (fun t => t) continuousAt_id rfl).eventually
      (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have ht : (1 : ℝ) < t := h2
    filter_upwards [(key t (by linarith)).eventually (gt_mem_nhds h1), hA t ht]
      with r h3 h4 using (ENNReal.div_le_div_right h4.2 _).trans_lt h3

end GlobalTheory.CompactDualQuot
