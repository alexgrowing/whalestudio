import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerProdCountMulDensityLeTwo
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DensityIntegral

theorem integral_cube (a : ℕ) (c : Fin a → ℕ) (hc : ∀ i, 1 ≤ c i) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1), ∏ i, (c i : ℝ) * τ i ^ (c i - 1) = 1 := by
  rw [volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (i : Fin a) (t : ℝ) => (c i : ℝ) * t ^ (c i - 1))]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, integral_pow]
  obtain ⟨m, hm⟩ : ∃ m, c i = m + 1 := ⟨c i - 1, by have := hc i; omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel, one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, sub_zero]
  push_cast
  field_simp

theorem dens_le (n f a : ℕ) (j : Fin a → ℕ) (hf : 1 ≤ f) (hj : ∀ i, 1 ≤ j i) (hn : 2 * ∑ i, j i + 1 ≤ n)
    (τ : Fin a → ℝ) (hτ : τ ∈ simplexH a) :
    FlagMeas.dens n f j τ ≤ ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) := by
  have h2 := (GlobalTheory.Count.layerProd_count_mul_density_le_two n f (∑ i, j i) a j τ 0 le_rfl (by omega)
    hτ.1 hτ.2 le_rfl (by norm_num)).2
  have h3 : 0 ≤ ∏ i, 2 * (f : ℝ) * j i / τ i :=
    Finset.prod_nonneg fun i _ => by have := (hτ.2 i).1; positivity
  refine (mul_le_mul_of_nonneg_right h2 h3).trans ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => by have := (hτ.2 i).1; positivity) fun i _ => ?_
  obtain ⟨h0, h1⟩ := hτ.2 i
  have hc : 1 ≤ 2 * f * j i := Nat.mul_pos (by omega) (hj i)
  have he : 2 * f * j i ≤ 2 * j i * (n - 2 * ∑ l, j l) * f := by
    calc 2 * f * j i = 2 * j i * 1 * f := by ring
      _ ≤ _ := by gcongr; omega
  have h4 : τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) ≤ τ i ^ (2 * f * j i - 1) * τ i := by
    rw [← pow_succ]
    exact pow_le_pow_of_le_one h0.le (by linarith) (by omega)
  calc _ ≤ τ i ^ (2 * f * j i - 1) * τ i * (2 * (f : ℝ) * j i / τ i) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = _ := by push_cast; field_simp

theorem lintegral_dens_le_one : ∀ (n f a : ℕ) (j : Fin a → ℕ), 1 ≤ f → (∀ i, 1 ≤ j i) → 2 * ∑ i, j i + 1 ≤ n → ∫⁻ τ in simplexH a, ENNReal.ofReal (dens n f j τ) ≤ 1 := by
  intro n f a j hf hj hn
  set box : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1) with hbox
  have hc : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : simplexH a ⊆ box := fun τ hτ i _ => ⟨(hτ.2 i).1.le, by linarith [(hτ.2 i).2]⟩
  have hm : MeasurableSet (simplexH a) := by
    have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
        ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
      ext τ
      simp [simplexH, StrictMono]
    rw [this]
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k))
      (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const))
  set g : (Fin a → ℝ) → ℝ := fun τ => ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) with hg
  have hcont : Continuous g := by rw [hg]; fun_prop
  have hint : IntegrableOn g box := hcont.continuousOn.integrableOn_compact hc
  calc _ ≤ ∫⁻ τ in simplexH a, ENNReal.ofReal (g τ) :=
        setLIntegral_mono' hm fun τ hτ => ENNReal.ofReal_le_ofReal (dens_le n f a j hf hj hn τ hτ)
    _ ≤ ∫⁻ τ in box, ENNReal.ofReal (g τ) := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ τ in box, g τ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        refine (ae_restrict_iff' hc.measurableSet).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
        refine Finset.prod_nonneg fun i _ => ?_
        have := (hτ i trivial).1
        positivity
    _ = 1 := by
        rw [integral_cube a (fun i => 2 * f * j i) fun i => Nat.mul_pos (by omega) (hj i), ENNReal.ofReal_one]

end GlobalTheory.DensityIntegral
