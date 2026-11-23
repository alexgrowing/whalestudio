import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open Filter Topology
open scoped SchwartzMap Uniformity

namespace GlobalTheory

theorem schwartz_family_uniform_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (I : Type)
    (lam : I → SchwartzMap V ℂ →L[ℂ] ℂ) (w : I → ℝ), (∀ i, 0 ≤ w i) →
    (∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖lam i f‖ ≤ C * w i ^ N) →
    ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)), ∀ i f,
      ‖lam i f‖ ≤ C * (T.sup (schwartzSeminormFamily ℂ V ℂ)) f * w i ^ N := by
  intro V _ _ _ I lam w hw hb
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BaireSpace 𝓢(V, ℂ) := inferInstance
  let S : ℕ × ℕ → Set 𝓢(V, ℂ) := fun p => {f | ∀ i, ‖lam i f‖ ≤ (p.2 : ℝ) * w i ^ p.1}
  have hS : ∀ p, IsClosed (S p) := by
    intro p
    simp only [S, Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_norm.comp (lam i).continuous) continuous_const
  have hU : ⋃ p, S p = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    obtain ⟨N, C, hC⟩ := hb f
    obtain ⟨M, hM⟩ := exists_nat_ge C
    exact Set.mem_iUnion.2 ⟨(N, M), fun i =>
      (hC i).trans (mul_le_mul_of_nonneg_right hM (pow_nonneg (hw i) _))⟩
  obtain ⟨p, f₀, hf₀⟩ := nonempty_interior_of_iUnion_of_closed hS hU
  have hn : interior (S p) ∈ 𝓝 f₀ := isOpen_interior.mem_nhds hf₀
  have hn' : (fun g => f₀ + g) ⁻¹' interior (S p) ∈ 𝓝 (0 : 𝓢(V, ℂ)) := by
    have h : Tendsto (fun g : 𝓢(V, ℂ) => f₀ + g) (𝓝 0) (𝓝 f₀) := by
      simpa using (continuous_const_add f₀).tendsto 0
    exact h hn
  obtain ⟨⟨T, ε⟩, hε, hT⟩ := ((schwartz_withSeminorms ℂ V ℂ).hasBasis_zero_ball).mem_iff.1 hn'
  simp only at hε hT
  set q := T.sup (schwartzSeminormFamily ℂ V ℂ) with hq
  have hball : ∀ g, q g < ε → ∀ i, ‖lam i g‖ ≤ 2 * (p.2 : ℝ) * w i ^ p.1 := by
    intro g hg i
    have h1 : f₀ + g ∈ S p := interior_subset (hT (by simpa [Seminorm.mem_ball] using hg))
    have h2 : f₀ ∈ S p := interior_subset hf₀
    have h3 : lam i g = lam i (f₀ + g) - lam i f₀ := by simp
    rw [h3]
    calc ‖lam i (f₀ + g) - lam i f₀‖ ≤ ‖lam i (f₀ + g)‖ + ‖lam i f₀‖ := norm_sub_le _ _
      _ ≤ (p.2 : ℝ) * w i ^ p.1 + (p.2 : ℝ) * w i ^ p.1 := add_le_add (h1 i) (h2 i)
      _ = 2 * (p.2 : ℝ) * w i ^ p.1 := by ring
  refine ⟨p.1, 2 * (p.2 : ℝ) / ε, T, fun i f => ?_⟩
  set A := 2 * (p.2 : ℝ) * w i ^ p.1 / ε with hA
  have hA0 : 0 ≤ A := by
    have := pow_nonneg (hw i) p.1
    positivity
  have hq0 : 0 ≤ q f := apply_nonneg _ _
  have hscale : ∀ t, q f < t → ‖lam i f‖ ≤ t * A := by
    intro t ht
    have htpos : 0 < t := lt_of_le_of_lt hq0 ht
    have hc : ‖((ε / t : ℝ) : ℂ)‖ = ε / t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (div_pos hε htpos).le]
    have hg : q (((ε / t : ℝ) : ℂ) • f) < ε := by
      rw [map_smul_eq_mul, hc]
      calc ε / t * q f < ε / t * t := mul_lt_mul_of_pos_left ht (div_pos hε htpos)
        _ = ε := by field_simp
    have h := hball _ hg i
    rw [map_smul, norm_smul, hc] at h
    rw [hA, show t * (2 * (p.2 : ℝ) * w i ^ p.1 / ε) = (t / ε) * (2 * (p.2 : ℝ) * w i ^ p.1) by ring]
    have : ‖lam i f‖ = (t / ε) * (ε / t * ‖lam i f‖) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h (div_pos htpos hε).le
  have hfin : ‖lam i f‖ ≤ q f * A := by
    rcases hA0.lt_or_eq with hApos | hAz
    · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      have : q f < a / A := (lt_div_iff₀ hApos).2 ha
      calc ‖lam i f‖ ≤ a / A * A := hscale _ this
        _ = a := by field_simp
    · rw [← hAz, mul_zero]
      have := hscale (q f + 1) (by linarith)
      rwa [← hAz, mul_zero] at this
  calc ‖lam i f‖ ≤ q f * A := hfin
    _ = 2 * (p.2 : ℝ) / ε * q f * w i ^ p.1 := by rw [hA]; ring

end GlobalTheory
