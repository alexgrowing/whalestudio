import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.InPairOfStab

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

section Gen

variable {Y : Type*} [MeasurableSpace Y]

theorem sigmaFinite_of_weight (ν : Measure Y) (W : Y → ℝ≥0∞) (hWm : Measurable W) (hWi : ∫⁻ y, W y ∂ν < ⊤)
    (hW0 : ν {y | W y = 0} = 0) : SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable
    (S := insert {y | W y = 0} (Set.range fun n : ℕ => {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y})) ?_ ?_ ?_
  · exact (Set.countable_range _).insert _
  · intro s hs
    rcases hs with rfl | ⟨n, rfl⟩
    · rw [hW0]
      exact ENNReal.zero_lt_top
    · calc ν {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y} ≤ (∫⁻ y, W y ∂ν) / ((n : ℝ≥0∞) + 1)⁻¹ :=
            meas_ge_le_lintegral_div hWm.aemeasurable (by simp) (by simp)
        _ < ⊤ := ENNReal.div_lt_top hWi.ne (by simp)
  · apply Set.eq_univ_of_forall
    intro y
    by_cases h : W y = 0
    · exact Set.mem_sUnion.2 ⟨_, Set.mem_insert _ _, h⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
      refine Set.mem_sUnion.2 ⟨_, Set.mem_insert_of_mem _ ⟨n, rfl⟩, ?_⟩
      show ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y
      exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

end Gen

def mStab (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (q : PairSp k r × Mt k r) : PairSp k r :=
  stabAct γ (Matrix.of q.2) q.1

def qG (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (q : Mt k r × Mt k r) : Mt k r :=
  Matrix.of.symm (γ⁻¹ * Matrix.of q.2 * γ * Matrix.of q.1)

theorem measurable_mStab (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (mStab (k := k) (r := r) γ) := by
  unfold mStab stabAct
  have c1 : Continuous (fun q : PairSp k r × Mt k r => (Matrix.of.symm (of q.2 * of q.1.1.2) : Mt k r)) :=
    continuous_snd.matrix_mul continuous_fst.fst.snd
  have c2 : Continuous (fun q : PairSp k r × Mt k r =>
      (Matrix.of.symm (γ⁻¹ * of q.2 * γ * of q.1.2.2) : Mt k r)) :=
    ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const).matrix_mul
      continuous_fst.snd.snd
  exact (measurable_fst.fst.fst.prodMk c1.measurable).prodMk (measurable_fst.snd.fst.prodMk c2.measurable)

theorem continuous_qG (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (qG (k := k) (r := r) γ) := by
  exact ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const).matrix_mul continuous_fst

section Cell

variable (L : LocBessel k r) {μG : Measure (Mt k r)} {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
  {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)}

theorem pairMeas_eq_map (hμR : IsHaarOn (RStab k r γ) μR) (hOQ : IsOrbQuot L γ μR ν) :
    pairMeas L = (ν.prod μR).map (mStab γ) := by
  haveI : SigmaFinite μR := hμR.1
  ext s hs
  have hf : Measurable (s.indicator (1 : PairSp k r → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one (μ := pairMeas L) hs,
    ← lintegral_indicator_one (μ := (ν.prod μR).map (mStab γ)) hs, hOQ _ hf,
    lintegral_map hf (measurable_mStab γ),
    lintegral_prod (fun q => s.indicator 1 (mStab γ q)) (hf.comp (measurable_mStab γ)).aemeasurable]
  rfl

theorem unfold_G (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ a, f (qG γ (x, a)) ∂μR ∂νR := by
  intro f hf
  rw [hQ f hf]
  refine lintegral_congr fun x => ?_
  have hc : Measurable (fun y : Mt k r => fun i j => (γ⁻¹ * Matrix.of y * γ) i j) := by
    have : Continuous (fun y : Mt k r => (Matrix.of.symm (γ⁻¹ * Matrix.of y * γ) : Mt k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hm : Measurable (fun s : Mt k r => f (fun i j => (of s * of x) i j)) := by
    have : Continuous (fun s : Mt k r => (Matrix.of.symm (of s * of x) : Mt k r)) :=
      continuous_id.matrix_mul continuous_const
    exact hf.comp this.measurable
  rw [lintegral_map hm hc]
  rfl

theorem muG_eq_map (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    μG = (νR.prod μR).map (qG γ) := by
  have : SigmaFinite μR := hμR.1
  exact map_of_unfold μG νR μR (qG γ) (continuous_qG γ).measurable (unfold_G hμR hQ)

theorem sigmaFinite_nuR (hμG : IsHaarOn (UH (Hpk k r)) μG) (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    SigmaFinite νR := by
  have : SigmaFinite μR := hμR.1
  have : SigmaFinite μG := hμG.1
  exact sigmaFinite_of_unfold μG νR μR hμR.2.1 (qG γ) (continuous_qG γ).measurable (unfold_G hμR hQ)

end Cell

end Formalism.MainNotions.S.Pv.AmpDDPf
