import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd

open MeasureTheory

namespace GlobalTheory.NMKProd

theorem lintegral_nmk {H : Type} [Mul H] [MeasurableSpace H] [MeasurableMul₂ H]
    (a b k : Measure H) [SFinite a] [SFinite b] [SFinite k] (d : H → ENNReal) (hd : Measurable d)
    (φ : H → ENNReal) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(((a.prod (b.prod k)).withDensity fun x => d x.2.1).map
        fun x : H × H × H => x.1 * x.2.1 * x.2.2) =
      ∫⁻ u, ∫⁻ m, d m * ∫⁻ z, φ (u * m * z) ∂k ∂b ∂a := by
  have hmul : Measurable (fun x : H × H × H => x.1 * x.2.1 * x.2.2) :=
    (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd
  have hD : Measurable (fun x : H × H × H => d x.2.1) := hd.comp measurable_snd.fst
  have hφm : Measurable (fun x : H × H × H => φ (x.1 * x.2.1 * x.2.2)) := hφ.comp hmul
  rw [lintegral_map hφ hmul, lintegral_withDensity_eq_lintegral_mul _ hD hφm,
    lintegral_prod _ (hD.mul hφm).aemeasurable]
  refine lintegral_congr fun u => ?_
  have hin : Measurable (fun y : H × H => d y.1 * φ (u * y.1 * y.2)) :=
    (hd.comp measurable_fst).mul (hφ.comp ((measurable_const.mul measurable_fst).mul measurable_snd))
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ hin.aemeasurable]
  refine lintegral_congr fun m => ?_
  have hz : Measurable (fun z : H => φ (u * m * z)) := hφ.comp (measurable_id.const_mul (u * m))
  exact lintegral_const_mul (d m) hz

private lemma indicator_pi_univ_eq_prod {ι : Type} [Fintype ι] {G : ι → Type} (s : ∀ i, Set (G i))
    (x : ∀ i, G i) :
    (Set.univ.pi s).indicator (1 : (∀ i, G i) → ENNReal) x =
      ∏ i, (s i).indicator (1 : G i → ENNReal) (x i) := by
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    rw [Set.mem_univ_pi] at hx
    simp [Set.indicator_of_mem (hx _)]
  · rw [Set.indicator_of_notMem hx]
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem prod_formula : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  intro ι _ G _ _ _ μ μN μM μK _ _ _ _ C c δ hC0 hCt hδ hrel φ hφ
  have hD : Measurable (fun m : ∀ i, G i => ∏ i, δ i (m i)) :=
    Finset.measurable_prod _ (fun i _ => (hδ i).comp (measurable_pi_apply i))
  have key := fun (ψ : (∀ i, G i) → ENNReal) (hψ : Measurable ψ) =>
    lintegral_nmk (Measure.pi μN) (Measure.pi μM) (Measure.pi μK)
      (fun m : ∀ i, G i => ∏ i, δ i (m i)) hD ψ hψ
  set R0 := (((Measure.pi μN).prod ((Measure.pi μM).prod (Measure.pi μK))).withDensity
      fun x => ∏ i, δ i (x.2.1 i)).map
    (fun x : (∀ i, G i) × (∀ i, G i) × (∀ i, G i) => x.1 * x.2.1 * x.2.2) with hR0
  have hC0' : (∏ i, C i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hC0 i
  have hCt' : (∏ i, C i) ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hCt i
  have hpi : Measure.pi μ = (∏ i, C i)⁻¹ • ((∏ i, c i) • R0) := by
    refine Measure.pi_eq fun s hs => ?_
    have hX : ∀ i, C i * μ i (s i) = c i * ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      intro i
      have h := hrel i ((s i).indicator 1) (measurable_one.indicator (hs i))
      rwa [lintegral_indicator_one (hs i)] at h
    have hbox : R0 (Set.univ.pi s) = ∏ i, ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      rw [← lintegral_indicator_one (MeasurableSet.univ_pi hs),
        key _ (measurable_one.indicator (MeasurableSet.univ_pi hs))]
      have hK : ∀ u m : ∀ i, G i, ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) =
          ∏ i, ∫⁻ k, (s i).indicator 1 (u i * m i * k) ∂(μK i) := by
        intro u m
        simp_rw [indicator_pi_univ_eq_prod]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun i k => (s i).indicator 1 (u i * m i * k))
          (fun i => (measurable_one.indicator (hs i)).comp (measurable_const.mul measurable_id))
      have hA : ∀ i (u' : G i), Measurable (fun m' : G i =>
          δ i m' * ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i)) := by
        intro i u'
        refine (hδ i).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun y : G i × G i => (s i).indicator 1 (u' * y.1 * y.2))
          ((measurable_one.indicator (hs i)).comp ((measurable_const.mul measurable_fst).mul measurable_snd))
      have hB : ∀ i, Measurable (fun u' : G i => ∫⁻ m', δ i m' *
          ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i) ∂(μM i)) := by
        intro i
        refine Measurable.lintegral_prod_right' (f := fun y : G i × G i =>
          δ i y.2 * ∫⁻ k, (s i).indicator 1 (y.1 * y.2 * k) ∂(μK i)) ?_
        refine ((hδ i).comp measurable_snd).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun z : (G i × G i) × G i =>
            (s i).indicator 1 (z.1.1 * z.1.2 * z.2))
          ((measurable_one.indicator (hs i)).comp
            ((measurable_fst.fst.mul measurable_fst.snd).mul measurable_snd))
      have hM : ∀ u : ∀ i, G i, ∫⁻ m, (∏ i, δ i (m i)) *
          ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) =
          ∏ i, ∫⁻ m', δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i) ∂(μM i) := by
        intro u
        simp_rw [hK u, ← Finset.prod_mul_distrib]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod
          (fun i m' => δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i)) (fun i => hA i (u i))
      simp_rw [hM]
      exact GlobalTheory.SnMass.Push.lintegral_fintype_prod _ hB
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [hbox, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => (hX i).symm,
      Finset.prod_mul_distrib, ← mul_assoc, ENNReal.inv_mul_cancel hC0' hCt', one_mul]
  rw [hpi, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hC0' hCt', one_mul, hR0]
  exact congrArg ((∏ i, c i) * ·) (key φ hφ)

end GlobalTheory.NMKProd
