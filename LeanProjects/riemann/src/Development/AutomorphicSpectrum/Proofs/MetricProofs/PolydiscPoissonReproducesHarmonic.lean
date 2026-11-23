import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PoissonIntegralPuncturedDisc
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem pker_eq {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    pker ρ w t = (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  simp only [pker, poissonKernel_def, sub_zero, h]

theorem sub_le_norm_circleMap_sub {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    ρ - ‖w‖ ≤ ‖circleMap 0 ρ t - w‖ := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  have h2 := norm_sub_norm_le (circleMap (0 : ℂ) ρ t) w
  rwa [h] at h2

theorem continuous_pker {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    Continuous (pker ρ w) := by
  have h : pker ρ w = fun t => (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 :=
    funext (pker_eq hρ w)
  rw [h]
  refine continuous_const.div
    (((continuous_circleMap 0 ρ).sub continuous_const).norm.pow 2) ?_
  intro t
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h2 : 0 < ‖circleMap (0 : ℂ) ρ t - w‖ := by linarith
  positivity

theorem exists_abs_pker_le {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    ∃ K : ℝ, ∀ t, |pker ρ w t| ≤ K := by
  refine ⟨(ρ ^ 2 - ‖w‖ ^ 2) / (ρ - ‖w‖) ^ 2, fun t => ?_⟩
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h0 : 0 < ρ - ‖w‖ := by linarith
  have hn : 0 ≤ ρ ^ 2 - ‖w‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg w) hw.le 2
    linarith
  rw [pker_eq hρ, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left hn (by positivity) (pow_le_pow_left₀ h0.le h1 2)

theorem continuous_torusPt {n : ℕ} (ρ : ℝ) : Continuous (torusPt (n := n) ρ) :=
  continuous_pi fun i => (continuous_circleMap 0 ρ).comp (continuous_apply i)

theorem circleMap_mem {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (t : ℝ) :
    circleMap (0 : ℂ) ρ t ≠ 0 ∧ ‖circleMap (0 : ℂ) ρ t‖ < R := by
  refine ⟨circleMap_ne_center hρ.ne', ?_⟩
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  rwa [h]

theorem torusPt_mem_punct {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (θ : Fin n → ℝ) :
    torusPt ρ θ ∈ punct R := fun i => circleMap_mem hρ hρR (θ i)

theorem cons_mem_punct {n : ℕ} {R : ℝ} {c : ℂ} {y : Fin n → ℂ} (hc : c ≠ 0 ∧ ‖c‖ < R)
    (hy : y ∈ punct R) : (Fin.cons c y : Fin (n + 1) → ℂ) ∈ punct R := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hc
  · simpa using hy j

theorem continuous_cons_pair {n : ℕ} {α : Type*} [TopologicalSpace α] :
    Continuous (fun p : α × (Fin n → α) => (Fin.cons p.1 p.2 : Fin (n + 1) → α)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

theorem integral_pi_cons {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (hF : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))) :
    ∫ θ, F θ ∂(Measure.pi fun _ : Fin (n + 1) => angMeas) =
      ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas := by
  have mp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))
      (Measure.pi fun _ : Fin (n + 1) => angMeas) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => angMeas) 0).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p =
        Fin.cons p.1 p.2 := by
    rintro ⟨a, b⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
  rw [← mp.integral_comp']
  simp only [he]
  exact integral_prod _ hF

theorem polyPoisson_eq_self : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R →
    ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) →
    ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  intro n
  induction n with
  | zero =>
    intro f ρ R M _ _ _ _ _ z _
    have h : ∀ θ : Fin 0 → ℝ, (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) = f z := by
      intro θ
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      rw [Subsingleton.elim (torusPt ρ θ) z]
    simp only [polyPoisson, h]
    simp
  | succ n ih =>
    intro f ρ R M hρ hρR hc hs hb z hz
    have hz0 := hz 0
    have hzt : Fin.tail z ∈ punct ρ := fun i => hz i.succ
    have hztR : Fin.tail z ∈ punct R := fun i => ⟨(hzt i).1, (hzt i).2.trans hρR⟩
    have hslice : ∀ t, polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) =
        f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) := by
      intro t
      have hcm := circleMap_mem (t := t) hρ hρR
      refine ih _ ρ R M hρ hρR ?_ ?_ ?_ _ hzt
      · have hcont : Continuous (fun y : Fin n → ℂ =>
            (Fin.cons (circleMap 0 ρ t) y : Fin (n + 1) → ℂ)) :=
          continuous_cons_pair.comp (continuous_const.prodMk continuous_id)
        exact hc.comp hcont.continuousOn (fun y hy => cons_mem_punct hcm hy)
      · intro y hy i
        have h := hs _ (cons_mem_punct hcm hy) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      · exact fun y hy => hb _ (cons_mem_punct hcm hy)
    have hone := GlobalTheory.CompanionTheory.Ar.PuncturedDisc.poisson_formula_punctured (fun w => f (Fin.cons w (Fin.tail z))) ρ R M hρ hρR
      (fun w hw0 hwR => by
        have h := hs _ (cons_mem_punct ⟨hw0, hwR⟩ hztR) 0
        simpa only [Fin.update_cons_zero, Fin.cons_zero] using h)
      (fun w hw0 hwR => hb _ (cons_mem_punct ⟨hw0, hwR⟩ hztR))
      (z 0) hz0.1 hz0.2
    simp only [Fin.cons_self_tail] at hone
    set F : (Fin (n + 1) → ℝ) → ℝ :=
      fun θ => (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) with hFdef
    have hFc : Continuous F :=
      (continuous_finsetProd _ fun i _ =>
        (continuous_pker hρ (hz i).2).comp (continuous_apply i)).mul
      (hc.comp_continuous (continuous_torusPt ρ) (torusPt_mem_punct hρ hρR))
    have hFb : ∃ K, ∀ θ, |F θ| ≤ K := by
      choose K hK using fun i => exists_abs_pker_le hρ (hz i).2
      refine ⟨(∏ i, K i) * M, fun θ => ?_⟩
      rw [hFdef]
      simp only [abs_mul, Finset.abs_prod]
      have hM : 0 ≤ M := (abs_nonneg _).trans (hb _ (torusPt_mem_punct hρ hρR θ))
      have hK0 : 0 ≤ ∏ i, K i :=
        Finset.prod_nonneg fun i _ => (abs_nonneg _).trans (hK i 0)
      exact mul_le_mul
        (Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hK i _))
        (hb _ (torusPt_mem_punct hρ hρR θ)) (abs_nonneg _) hK0
    obtain ⟨K, hK⟩ := hFb
    have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
        (angMeas.prod (Measure.pi fun _ : Fin n => angMeas)) :=
      Integrable.of_bound (hFc.comp continuous_cons_pair).aestronglyMeasurable K
        (ae_of_all _ fun p => hK _)
    have hFcons : ∀ t θ', F (Fin.cons t θ') = pker ρ (z 0) t *
        ((∏ i, pker ρ (Fin.tail z i) (θ' i)) *
          f (Fin.cons (circleMap 0 ρ t) (torusPt ρ θ'))) := by
      intro t θ'
      have ht : torusPt ρ (Fin.cons t θ' : Fin (n + 1) → ℝ) =
          Fin.cons (circleMap 0 ρ t) (torusPt ρ θ') := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusPt]
      simp only [hFdef, ht, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, mul_assoc]
    calc polyPoisson ρ f z
        = ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas :=
          integral_pi_cons F hint
      _ = ∫ t, pker ρ (z 0) t * f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) ∂angMeas := by
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          have h : ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) =
              pker ρ (z 0) t *
                polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) := by
            simp only [hFcons]
            rw [integral_const_mul]
            rfl
          simp only [h, hslice t]
      _ = f z := hone

end GlobalTheory.CompanionTheory.Ar.PB.Flat
