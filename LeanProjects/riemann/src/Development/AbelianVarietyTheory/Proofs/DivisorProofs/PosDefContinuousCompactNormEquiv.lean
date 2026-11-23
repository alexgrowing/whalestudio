import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

namespace GlobalTheory

theorem posDef_family_gnorm_comparable : ∀ (e n : ℕ) (K : Set (Fin e → ℂ)) (H₀ : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), IsCompact K → ContinuousOn H₀ K → (∀ z ∈ K, (H₀ z).PosDef) → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ K, ∀ v : Fin n → ℂ, c * ‖v‖ ≤ GlobalTheory.HermFrame.gnorm (H₀ z) v ∧ GlobalTheory.HermFrame.gnorm (H₀ z) v ≤ C * ‖v‖ := by
  intro e n K H₀ hK hc hp'
  obtain ⟨f, hfdef⟩ : ∃ f : (Fin e → ℂ) × (Fin n → ℂ) → ℝ,
      f = fun p => (HermFrame.form (H₀ p.1) p.2 p.2).re := ⟨_, rfl⟩
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : Fin n → ℂ) 1) := hK.prod (isCompact_sphere _ _)
  have hform : Continuous fun q : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) =>
      HermFrame.form q.1 q.2 q.2 := by
    unfold HermFrame.form
    fun_prop
  have hf : ContinuousOn f (K ×ˢ Metric.sphere (0 : Fin n → ℂ) 1) := by
    have h1 : ContinuousOn (fun p : (Fin e → ℂ) × (Fin n → ℂ) => (H₀ p.1, p.2))
        (K ×ˢ Metric.sphere (0 : Fin n → ℂ) 1) := by
      apply ContinuousOn.prodMk
      · exact hc.comp continuousOn_fst (fun p hp => hp.1)
      · exact continuousOn_snd
    have h3 := Complex.continuous_re.comp_continuousOn (hform.comp_continuousOn h1)
    rw [hfdef]
    exact h3
  have hfpos : ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin n → ℂ) 1, 0 < f p := by
    intro p hp
    have hne : p.2 ≠ 0 := by
      intro h
      have h2 := hp.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at h2
      exact zero_ne_one h2
    rw [hfdef]
    exact (Complex.lt_def.1 ((HermFrame.posDef_iff.1 (hp' p.1 hp.1)).2 p.2 hne)).1
  obtain ⟨c2, C2, hc2, hC2, hb⟩ : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin n → ℂ) 1, a ≤ f p ∧ f p ≤ b := by
    rcases (K ×ˢ Metric.sphere (0 : Fin n → ℂ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, 1, one_pos, one_pos, by simp [h]⟩
    · obtain ⟨p0, hp0, hmin⟩ := hS.exists_isMinOn h hf
      obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hf
      refine ⟨f p0, max B 1, hfpos p0 hp0, lt_of_lt_of_le one_pos (le_max_right _ _),
        fun p hp => ⟨hmin hp, ?_⟩⟩
      exact (Real.le_norm_self _).trans ((hB p hp).trans (le_max_left _ _))
  refine ⟨Real.sqrt c2, Real.sqrt C2, Real.sqrt_pos.2 hc2, Real.sqrt_pos.2 hC2, fun z hz v => ?_⟩
  have hH := (hp' z hz).posSemidef
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  obtain ⟨u, hu⟩ : ∃ u : Fin n → ℂ, u = ((‖v‖⁻¹ : ℝ) : ℂ) • v := ⟨_, rfl⟩
  have hu1 : u ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_norm, inv_mul_cancel₀ hnv.ne']
  have hvu : v = ((‖v‖ : ℝ) : ℂ) • u := by
    rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnv.ne', Complex.ofReal_one, one_smul]
  have hg : HermFrame.gnorm (H₀ z) v = ‖v‖ * HermFrame.gnorm (H₀ z) u := by
    conv_lhs => rw [hvu]
    rw [HermFrame.gnorm_smul hH, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hgu : HermFrame.gnorm (H₀ z) u = Real.sqrt (f (z, u)) := by rw [hfdef]; rfl
  obtain ⟨h1, h2⟩ := hb (z, u) ⟨hz, hu1⟩
  rw [hg, hgu]
  constructor
  · rw [mul_comm (Real.sqrt c2)]; exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hnv.le
  · rw [mul_comm (Real.sqrt C2)]; exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) hnv.le

end GlobalTheory
