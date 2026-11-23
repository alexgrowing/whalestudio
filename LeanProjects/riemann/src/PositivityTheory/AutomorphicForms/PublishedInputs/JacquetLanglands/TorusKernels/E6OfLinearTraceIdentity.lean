import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.LinearTraceIdentity

open UpperTheory.Esk

theorem op_kern {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf)
    (y : D.Y) (hs : ∀ i, Summable fun γ : PG F =>
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * (D.rep y.1 * a i)) * (qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2)) :
    Dat.Op a (D.Kern k y) (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
  show ∑ i, D.Kern k y (y.2, D.rep y.1 * a i) = ∑' γ : PG F, D.kk k a γ y
  simp only [Dat.Kern, Dat.kk, Dat.kt, Dat.Te]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  refine tsum_congr fun γ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

end UpperTheory.Esk.LinearTraceIdentity

theorem UpperTheory.Esk.e6_of_linear_trace_identity : UpperTheory.Esk.E0a → UpperTheory.Esk.FormsStableUnderOperators → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E3 → UpperTheory.Esk.E4 → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.E5 → UpperTheory.Esk.LinTr → UpperTheory.Esk.E6 := by
  intro hE0a hE0b _ hE3 hE4 hE4b hE5 hLin
  intro F I Gf ι _ _ _ _ D k a hH hfd h b hb
  have hM : ∀ f, f ∈ D.M k ↔ D.IsForm k f := (hE0b F I Gf D hH.ax k).1
  have hE4' := hE4 F I Gf D hH.ax k hH.four hH.compat
  have hE4b' := hE4b F I Gf D hH.ax k hH.four hH.compat
  have hE5' := hE5 F I Gf D hH.ax k hH.four hH.compat b hb
  have hbm : Measurable fun y => (b y).toNNReal := hb.meas.real_toNNReal
  obtain ⟨ν, hν⟩ : ∃ ν : Measure D.Y, ν = D.μY.withDensity fun y => ((b y).toNNReal : ℝ≥0∞) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]
    exact MeasureTheory.isFiniteMeasure_withDensity (hE3 F I Gf D hH.ax b hb).ne
  have hint : ∀ g : D.Y → ℂ, ∫ y, g y ∂ν = ∫ y, b y • g y ∂D.μY := by
    intro g
    rw [hν, integral_withDensity_eq_integral_smul hbm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  obtain ⟨K, hK⟩ : ∃ K : D.Y → D.M k, ∀ y, (K y).1 = D.Kern k y :=
    ⟨fun y => ⟨D.Kern k y, (hM _).2 (hE4' y)⟩, fun _ => rfl⟩
  have hn0 : Measurable fun z : X I => nrm k z := by
    unfold nrm
    refine Finset.measurable_prod _ fun v _ => ?_
    exact (continuous_abs.measurable.comp
      (Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))).pow_const _
  have hn_meas : Measurable fun y : D.Y => nrm k y.2 := hn0.comp measurable_snd
  have hn_pos : ∀ y : D.Y, 0 < nrm k y.2 := fun y =>
    Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.mpr (y.2 v).2) _
  have hK_meas : ∀ p, Measurable fun y => (K y).1 p := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.1
  have hf_meas : ∀ f : D.M k, Measurable fun y : D.Y => f.1 (y.2, D.rep y.1) := by
    intro f
    have hF := (hM f.1).1 f.2
    haveI : Countable D.Om := hH.ax.cO
    refine measurable_from_prod_countable_right fun ω => ?_
    have hc : Measurable fun z : X I => f.1 (z, D.rep ω) := ((hF.hol (D.rep ω)).1).measurable
    exact hc
  have hK_bdd : ∀ p, ∃ C, ∀ y, ‖(K y).1 p‖ ≤ C * nrm k y.2 := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.2
  have hf_bdd : ∀ f : D.M k, ∃ C, ∀ y : D.Y, ‖f.1 (y.2, D.rep y.1)‖ * nrm k y.2 ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := ((hM f.1).1 f.2).bdd
    exact ⟨C, fun y => hC _ _⟩
  have hrep : ∀ (f : D.M k) p, ∫ y, (K y).1 p * f.1 (y.2, D.rep y.1) ∂ν = f.1 p := by
    intro f p
    rw [hint]
    simp only [hK]
    exact hE5' f.1 ((hM f.1).1 f.2) p
  obtain ⟨hmeas, ⟨C, hC⟩, htr⟩ := hLin (X I × Gf) D.Y ν (D.M k) ((Dat.Op a).restrict h) K
    (fun y => (y.2, D.rep y.1)) (fun y => nrm k y.2) hn_meas hn_pos hK_meas hf_meas hK_bdd hf_bdd hrep
  have hval : ∀ y : D.Y, ((Dat.Op a).restrict h (K y)).1 (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
    intro y
    rw [LinearMap.restrict_coe_apply, hK]
    exact LinearTraceIdentity.op_kern D k a y (fun i => ((hE4b' (y.2, D.rep y.1 * a i)).1 y).of_norm)
  have hm2 : Measurable fun y => ∑' γ : PG F, D.kk k a γ y := by
    simpa only [hval] using hmeas
  refine ⟨?_, ?_⟩
  · have hgi : Integrable (fun y => ∑' γ : PG F, D.kk k a γ y) ν := by
      refine (integrable_const C).mono' hm2.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      have := hC y
      simp only [hval] at this
      exact this
    rw [hν, MeasureTheory.integrable_withDensity_iff_integrable_smul hbm] at hgi
    refine hgi.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  · rw [htr, hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hval]
