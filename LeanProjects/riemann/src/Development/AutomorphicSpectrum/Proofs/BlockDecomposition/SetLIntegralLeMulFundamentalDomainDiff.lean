import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Unfolding

theorem setLIntegral_le_mul_fundamentalDomain_diff {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (F S T : Set G) (hF : IsFundamentalDomain Γ F μ) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : G → ℝ≥0∞) (hh : Measurable h)
    (hinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (hST : ∀ γ ∈ Γ, ∀ x, γ * x ∈ S → x ∉ T) :
    ∫⁻ x in S, h x ∂μ ≤ N * ∫⁻ x in F \ T, h x ∂μ := by
  have hmeas : ∀ γ : Γ, Measurable (fun x : G => S.indicator h (γ • x)) := fun γ =>
    (hh.indicator hS).comp (measurable_const_smul γ)
  have h1 : ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := by
    rw [← lintegral_indicator hS]
    exact hF.lintegral_eq_tsum'' _
  have hpt : ∀ x, ∑' γ : Γ, S.indicator h (γ • x) ≤ N * Tᶜ.indicator h x := by
    intro x
    by_cases hx : x ∈ T
    · have hz : ∀ γ : Γ, S.indicator h (γ • x) = 0 := fun γ => by
        apply Set.indicator_of_notMem
        intro hmem
        exact hST γ γ.2 x (by simpa [Subgroup.smul_def] using hmem) hx
      simp [hz]
    · have hrew : ∀ γ : Γ, S.indicator h (γ • x) =
          ({γ : Γ | (γ : G) * x ∈ S}).indicator (fun _ => h x) γ := fun γ => by
        by_cases hg : (γ : G) * x ∈ S
        · rw [Set.indicator_of_mem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_mem hg, hinv γ γ.2 x]
        · rw [Set.indicator_of_notMem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_notMem hg]
      simp_rw [hrew]
      rw [← tsum_subtype, ENNReal.tsum_set_const,
        Set.indicator_of_mem (show x ∈ Tᶜ from hx)]
      gcongr
      have hc := ENat.toENNReal_le.mpr (hN x)
      simpa using hc
  calc ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := h1
    _ = ∫⁻ x in F, ∑' γ : Γ, S.indicator h (γ • x) ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ ≤ ∫⁻ x in F, (N : ℝ≥0∞) * Tᶜ.indicator h x ∂μ := lintegral_mono hpt
    _ = N * ∫⁻ x in F, Tᶜ.indicator h x ∂μ :=
        lintegral_const_mul _ (hh.indicator hT.compl)
    _ = N * ∫⁻ x in F \ T, h x ∂μ := by
        rw [setLIntegral_indicator hT.compl, Set.inter_comm, Set.diff_eq]

end GlobalTheory.CompanionTheory.Unfolding
