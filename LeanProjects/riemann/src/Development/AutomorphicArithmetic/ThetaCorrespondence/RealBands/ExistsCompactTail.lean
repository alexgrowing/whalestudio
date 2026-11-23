import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

private theorem exists_compact_tail {G : Type} [TopologicalSpace G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ)
    (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Set G, IsCompact D ∧ ∫ g, Dᶜ.indicator (fun g => ‖f g‖) g ∂μ ≤ ε := by
  have hm : ∀ n, MeasurableSet (compactCovering G n)ᶜ := fun n =>
    (isCompact_compactCovering G n).isClosed.measurableSet.compl
  have ht : Tendsto (fun n => ∫ g, (compactCovering G n)ᶜ.indicator (fun g => ‖f g‖) g ∂μ) atTop
      (𝓝 (∫ _g, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun g => ‖f g‖)
      (fun n => (hf.norm.indicator (hm n)).aestronglyMeasurable) hf.norm (fun n => ?_) ?_
    · refine Eventually.of_forall fun g => ?_
      simpa using norm_indicator_le_norm_self (s := (compactCovering G n)ᶜ) (fun g => ‖f g‖) g
    · refine Eventually.of_forall fun g => ?_
      obtain ⟨n, hn⟩ := exists_mem_compactCovering g
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with m hm'
      have : g ∈ compactCovering G m := compactCovering_subset G hm' hn
      simp [this]
  rw [integral_zero] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds hε)).exists
  exact ⟨_, isCompact_compactCovering G n, hn⟩

private theorem isEig_twist {G : Type} [Group G] [TopologicalSpace G] {N : Set G} {a : ℝ → G} {H : G → ℝ}
    (hr : IsRay N a H) {s s' C : ℝ} {h : G → ℂ} (hh : IsEig N a s' C h) :
    IsEig N a s C (fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g) := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hH := hr.contH
  refine ⟨by fun_prop, fun g => ?_, fun g m hm => ?_, fun g t => ?_⟩
  · rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]; exact h2 g
  · simp only [hr.inv g m hm, h3 g m hm]
  · simp only [hr.move g t, h4 g t]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem UpperTheory.Lit.Cusp.opLe_near :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s s' r : ℝ, |s - s'| < δ → OpLe μ N a f s r → OpLe μ N a f s' (r + ε) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hr hf ε hε
  obtain ⟨D, hD, hDε⟩ := exists_compact_tail μ f hf (ε / 4) (by positivity)
  obtain ⟨c, hc⟩ := hr.bdd D hD
  have hmD : MeasurableSet Dᶜ := hD.isClosed.measurableSet.compl
  set A : ℝ := ∫ g, ‖f g‖ ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun g => norm_nonneg _
  set δ : ℝ := ε / 2 / ((|c| + 1) * (A + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : δ * ((|c| + 1) * (A + 1)) = ε / 2 := by rw [hδ]; field_simp
  refine ⟨δ, hδ0, fun s s' r hs hop C h hh x => ?_⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hh.2.1 1)
  have ht := isEig_twist (s := s) hr hh
  have h1 := hop C _ ht x
  have hint : ∀ {t : ℝ} {k : G → ℂ}, IsEig N a t C k → Integrable (fun g => f g * k (g⁻¹ * x)) μ := by
    intro t k hk
    have hk1 := hk.1
    have hc : Continuous fun g : G => k (g⁻¹ * x) := by fun_prop
    exact hf.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun g => hk.2.1 _)
  set u : ℂ := Complex.exp (Complex.I * ((-((s - s') * H x) : ℝ) : ℂ)) with hu
  have hu1 : ‖u‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  set k : G → ℂ := fun g => Complex.exp (Complex.I * (((s - s') * H g : ℝ) : ℂ)) * h g with hk
  have hdiff : u * conv μ f k x - conv μ f h x
      = ∫ g, (u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)) ∂μ := by
    rw [integral_sub ((hint ht).const_mul u) (hint hh), integral_const_mul]
    rfl
  have hpt : ∀ g, ‖u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)‖
      ≤ C * (δ * (|c| + 1) * ‖f g‖ + 2 * Dᶜ.indicator (fun g => ‖f g‖) g) := by
    intro g
    have e : u * (f g * k (g⁻¹ * x)) - f g * h (g⁻¹ * x)
        = h (g⁻¹ * x) * ((Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1) * f g) := by
      have : Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ))
          = u * Complex.exp (Complex.I * (((s - s') * H (g⁻¹ * x) : ℝ) : ℂ)) := by
        rw [hu, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [this, hk]; ring
    rw [e, norm_mul, norm_mul]
    refine mul_le_mul (hh.2.1 _) ?_ (by positivity) hC
    by_cases hg : g ∈ D
    · have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (s - s') * (H (g⁻¹ * x) - H x))
      have h3 : ‖(s - s') * (H (g⁻¹ * x) - H x)‖ ≤ δ * (|c| + 1) := by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hs.le ((hc g hg x).trans (by linarith [le_abs_self c])) (abs_nonneg _) hδ0.le
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = 0 := by simp [hg]
      rw [h4, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg _)
    · have h2 : ‖Complex.exp (Complex.I * (((s - s') * (H (g⁻¹ * x) - H x) : ℝ) : ℂ)) - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num
      have h4 : Dᶜ.indicator (fun g => ‖f g‖) g = ‖f g‖ := by simp [hg]
      rw [h4]
      have h5 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (f g))
      have h6 : 0 ≤ δ * (|c| + 1) * ‖f g‖ := by positivity
      linarith
  have hi1 : Integrable (fun g => δ * (|c| + 1) * ‖f g‖) μ := hf.norm.const_mul _
  have hi2 : Integrable (fun g => 2 * Dᶜ.indicator (fun g => ‖f g‖) g) μ :=
    (hf.norm.indicator hmD).const_mul _
  have hb : ‖u * conv μ f k x - conv μ f h x‖ ≤ C * ε := by
    rw [hdiff]
    refine (norm_integral_le_of_norm_le ((hi1.add hi2).const_mul C) (Eventually.of_forall hpt)).trans ?_
    simp only [Pi.add_apply]
    rw [integral_const_mul, integral_add hi1 hi2, integral_const_mul, integral_const_mul, ← hA]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have : 0 ≤ δ * (|c| + 1) := by positivity
    nlinarith
  have h2 : ‖u * conv μ f k x‖ ≤ r * C := by rw [norm_mul, hu1, one_mul]; exact h1
  have h3 : ‖conv μ f h x‖ ≤ ‖u * conv μ f k x‖ + ‖u * conv μ f k x - conv μ f h x‖ := by
    simpa using norm_sub_le (u * conv μ f k x) (u * conv μ f k x - conv μ f h x)
  linarith
