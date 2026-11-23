import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
open scoped ENNReal

noncomputable section

namespace GlobalTheory.PiCoord

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
        (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ : Fin (n + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have split : ∀ p : E × (Fin n → E),
        (∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm p i)) =
          f 0 p.1 * ∏ j : Fin n, f j.succ (p.2 j) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp_rw [split]
    have hrest : Measurable fun z : Fin n → E => ∏ j : Fin n, f j.succ (z j) :=
      Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)
    rw [lintegral_prod_mul (hf 0).aemeasurable hrest.aemeasurable,
      ih (fun j => f j.succ) (fun j => hf j.succ), Fin.prod_univ_succ]

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e)
      (Measure.pi fun _ : Fin (Fintype.card ι) => μ) (Measure.pi fun _ : ι => μ) :=
    measurePreserving_piCongrLeft (fun _ : ι => μ) e
  calc ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ)
      = ∫⁻ y : Fin (Fintype.card ι) → E, ∏ j, f (e j) (y j) ∂(Measure.pi fun _ => μ) := by
        rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        refine lintegral_congr fun y => ?_
        rw [← e.prod_comp]
        simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    _ = ∏ j, ∫⁻ t, f (e j) t ∂μ := lintegral_pi_fin _ μ _ fun j => hf (e j)
    _ = ∏ i, ∫⁻ t, f i t ∂μ := e.prod_comp fun i => ∫⁻ t, f i t ∂μ

theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : ι → E, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x =
      ∏ i, (s i).indicator f (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ i)) f).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)).symm
  simp_rw [hind]
  rw [lintegral_pi_prod μ (fun i => (s i).indicator f) fun i => hf.indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

private theorem lintegral_indicator_one_mul_eq_setLIntegral {X : Type*} [MeasurableSpace X] (m : Measure X) {t : Set X}
    (ht : MeasurableSet t) (w : X → ℝ≥0∞) :
    ∫⁻ x, t.indicator 1 x * w x ∂m = ∫⁻ x in t, w x ∂m := by
  rw [← lintegral_indicator ht]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ t
  · simp [hx]
  · simp [hx]

theorem pi_change {ι P D : Type*} [Fintype ι] [MeasurableSpace P] [MeasurableSpace D]
    (μ : Measure P) (ν : Measure D) [SigmaFinite μ] [SigmaFinite ν] (c : P → D) (hc : Measurable c)
    (ρ : D → ℝ) (σ : P → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ g, 0 ≤ ρ g) (hσ0 : ∀ h, 0 ≤ σ h)
    (H : ∀ φ : D → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g * ENNReal.ofReal (ρ g) ∂ν = ∫⁻ p, φ (c p) * ENNReal.ofReal (σ p) ∂μ)
    (φ : (ι → D) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν) =
      ∫⁻ p : ι → P, φ (fun i => c (p i)) * ENNReal.ofReal (∏ i, σ (p i)) ∂(Measure.pi fun _ => μ) := by
  have hρm : Measurable fun g => ENNReal.ofReal (ρ g) := hρ.ennreal_ofReal
  have hσm : Measurable fun p => ENNReal.ofReal (σ p) := hσ.ennreal_ofReal
  have hmap : ν.withDensity (fun g => ENNReal.ofReal (ρ g)) =
      (μ.withDensity fun p => ENNReal.ofReal (σ p)).map c := by
    ext s hs
    rw [withDensity_apply _ hs, Measure.map_apply hc hs, withDensity_apply _ (hc hs)]
    have h1 := H (s.indicator 1) (measurable_one.indicator hs)
    rw [lintegral_indicator_one_mul_eq_setLIntegral ν hs] at h1
    have hpre : ∀ p, s.indicator (1 : D → ℝ≥0∞) (c p) = (c ⁻¹' s).indicator 1 p := by
      intro p
      by_cases hp : c p ∈ s
      · simp [hp]
      · simp [hp]
    simp_rw [hpre] at h1
    rw [lintegral_indicator_one_mul_eq_setLIntegral μ (hc hs)] at h1
    exact h1
  have hcm : Measurable fun (p : ι → P) (i : ι) => c (p i) :=
    measurable_pi_lambda _ fun i => hc.comp (measurable_pi_apply i)
  have : SigmaFinite ((μ.withDensity fun p => ENNReal.ofReal (σ p)).map c) := by
    rw [← hmap]; infer_instance
  have hprodρ : ∀ g : ι → D, ENNReal.ofReal (∏ i, ρ (g i)) = ∏ i, ENNReal.ofReal (ρ (g i)) :=
    fun g => ENNReal.ofReal_prod_of_nonneg fun i _ => hρ0 _
  have hprodσ : ∀ p : ι → P, ENNReal.ofReal (∏ i, σ (p i)) = ∏ i, ENNReal.ofReal (σ (p i)) :=
    fun p => ENNReal.ofReal_prod_of_nonneg fun i _ => hσ0 _
  have hdρ : Measurable fun g : ι → D => ∏ i, ENNReal.ofReal (ρ (g i)) :=
    Finset.measurable_prod _ fun i _ => hρm.comp (measurable_pi_apply i)
  have hdσ : Measurable fun p : ι → P => ∏ i, ENNReal.ofReal (σ (p i)) :=
    Finset.measurable_prod _ fun i _ => hσm.comp (measurable_pi_apply i)
  calc ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν)
      = ∫⁻ g, ((fun g : ι → D => ∏ i, ENNReal.ofReal (ρ (g i))) * φ) g ∂(Measure.pi fun _ => ν) := by
        refine lintegral_congr fun g => ?_
        rw [hprodρ, Pi.mul_apply, mul_comm]
    _ = ∫⁻ g, φ g ∂((Measure.pi fun _ : ι => ν).withDensity fun g => ∏ i, ENNReal.ofReal (ρ (g i))) :=
        (lintegral_withDensity_eq_lintegral_mul _ hdρ hφ).symm
    _ = ∫⁻ g, φ g ∂(Measure.pi fun _ : ι => ν.withDensity fun g => ENNReal.ofReal (ρ g)) := by
        rw [pi_withDensity ν _ hρm]
    _ = ∫⁻ g, φ g ∂(Measure.pi fun _ : ι => (μ.withDensity fun p => ENNReal.ofReal (σ p)).map c) := by
        rw [hmap]
    _ = ∫⁻ g, φ g ∂((Measure.pi fun _ : ι => μ.withDensity fun p => ENNReal.ofReal (σ p)).map
          fun (p : ι → P) (i : ι) => c (p i)) := by
        rw [Measure.pi_map_pi fun _ => hc.aemeasurable]
    _ = ∫⁻ p, φ (fun i => c (p i)) ∂(Measure.pi fun _ : ι => μ.withDensity fun p => ENNReal.ofReal (σ p)) :=
        lintegral_map hφ hcm
    _ = ∫⁻ p, φ (fun i => c (p i)) ∂((Measure.pi fun _ : ι => μ).withDensity
          fun p => ∏ i, ENNReal.ofReal (σ (p i))) := by
        rw [pi_withDensity μ _ hσm]
    _ = ∫⁻ p : ι → P, φ (fun i => c (p i)) * ENNReal.ofReal (∏ i, σ (p i)) ∂(Measure.pi fun _ => μ) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hdσ
          (show Measurable fun p : ι → P => φ (fun i => c (p i)) from hφ.comp hcm)]
        refine lintegral_congr fun p => ?_
        rw [hprodσ, Pi.mul_apply, mul_comm]

theorem lintegral_pi_prod_two {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (F : (ι → A × B) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F p ∂(Measure.pi fun _ => μ.prod ν) =
      ∫⁻ a : ι → A, ∫⁻ b : ι → B, F (fun i => (a i, b i)) ∂(Measure.pi fun _ => ν)
        ∂(Measure.pi fun _ => μ) := by
  have hp : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow A B ι)
      (Measure.pi fun _ : ι => μ.prod ν) ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => ν)) :=
    measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => μ) (fun _ => ν)
  rw [← hp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
    lintegral_prod (fun z => F ((MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm z))
      (show Measurable fun z => F ((MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm z) from
        hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
  rfl

theorem pi_change_three {ι A B C D : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (α : Measure A) (β : Measure B) (γ : Measure C) (ν : Measure D)
    [SigmaFinite α] [SigmaFinite β] [SigmaFinite γ] [SigmaFinite ν]
    (c : A → B → C → D) (hc : Measurable fun p : A × B × C => c p.1 p.2.1 p.2.2)
    (ρ : D → ℝ) (σ : B → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ g, 0 ≤ ρ g) (hσ0 : ∀ h, 0 ≤ σ h)
    (H : ∀ φ : D → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g * ENNReal.ofReal (ρ g) ∂ν =
        ∫⁻ x, ∫⁻ h, ∫⁻ T, φ (c x h T) * ENNReal.ofReal (σ h) ∂γ ∂β ∂α)
    (φ : (ι → D) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν) =
      ∫⁻ x : ι → A, ∫⁻ h : ι → B, ∫⁻ T : ι → C,
        φ (fun i => c (x i) (h i) (T i)) * ENNReal.ofReal (∏ i, σ (h i))
        ∂(Measure.pi fun _ => γ) ∂(Measure.pi fun _ => β) ∂(Measure.pi fun _ => α) := by
  have hσ' : Measurable fun p : A × B × C => σ p.2.1 := hσ.comp (measurable_fst.comp measurable_snd)
  have H' : ∀ ψ : D → ℝ≥0∞, Measurable ψ → ∫⁻ g, ψ g * ENNReal.ofReal (ρ g) ∂ν =
      ∫⁻ p, ψ (c p.1 p.2.1 p.2.2) * ENNReal.ofReal (σ p.2.1) ∂(α.prod (β.prod γ)) := by
    intro ψ hψ
    have m1 : Measurable fun p : A × B × C => ψ (c p.1 p.2.1 p.2.2) * ENNReal.ofReal (σ p.2.1) :=
      (hψ.comp hc).mul hσ'.ennreal_ofReal
    rw [H ψ hψ, lintegral_prod _ m1.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact (lintegral_prod (fun q : B × C => ψ (c x q.1 q.2) * ENNReal.ofReal (σ q.1))
      (m1.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
  rw [pi_change (α.prod (β.prod γ)) ν (fun p => c p.1 p.2.1 p.2.2) hc ρ (fun p => σ p.2.1) hρ hσ'
    hρ0 (fun p => hσ0 _) H' φ hφ]
  have hF : Measurable fun p : ι → A × B × C =>
      φ (fun i => c (p i).1 (p i).2.1 (p i).2.2) * ENNReal.ofReal (∏ i, σ (p i).2.1) :=
    (hφ.comp (measurable_pi_lambda _ fun i => hc.comp (measurable_pi_apply i))).mul
      (Finset.measurable_prod _ fun i _ => hσ'.comp (measurable_pi_apply i)).ennreal_ofReal
  rw [lintegral_pi_prod_two α (β.prod γ) _ hF]
  refine lintegral_congr fun x => ?_
  have hG : Measurable fun q : ι → B × C =>
      φ (fun i => c (x i) (q i).1 (q i).2) * ENNReal.ofReal (∏ i, σ (q i).1) :=
    hF.comp (measurable_pi_lambda _ fun i => (measurable_const.prodMk (measurable_pi_apply i)))
  exact lintegral_pi_prod_two β γ _ hG

theorem piCoord : ∀ (ι : Type) [Fintype ι] (k : ℕ) (c : (Fin (k + 1) → ℂ) → (Fin k → Fin k → ℂ) → (Fin k → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ), Measurable (fun p : (Fin (k + 1) → ℂ) × (Fin k → Fin k → ℂ) × (Fin k → ℂ) => c p.1 p.2.1 p.2.2) → ∀ (ρ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ℝ) (σ : (Fin k → Fin k → ℂ) → ℝ), Measurable ρ → Measurable σ → (∀ g, 0 ≤ ρ g) → (∀ h, 0 ≤ σ h) → (∀ φ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal (ρ g) = ∫⁻ x, ∫⁻ h, ∫⁻ T, φ (c x h T) * ENNReal.ofReal (σ h)) → ∀ φ : (ι → Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) = ∫⁻ x : ι → Fin (k + 1) → ℂ, ∫⁻ h : ι → Fin k → Fin k → ℂ, ∫⁻ T : ι → Fin k → ℂ, φ (fun i => c (x i) (h i) (T i)) * ENNReal.ofReal (∏ i, σ (h i)) := by
  intro ι _ k c hc ρ σ hρ hσ hρ0 hσ0 H φ hφ
  exact pi_change_three volume volume volume volume c hc ρ σ hρ hσ hρ0 hσ0 H φ hφ

end GlobalTheory.PiCoord
