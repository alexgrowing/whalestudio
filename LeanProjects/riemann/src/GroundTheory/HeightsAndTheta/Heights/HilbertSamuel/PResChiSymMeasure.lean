import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.MeasurableResPtHsmProjLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace ResChiSymMeasure

variable {κ : Type} [Fintype κ]

theorem eval_smul_of_homog {J R : Type*} [Fintype J] [CommRing R] {φ : MvPolynomial J R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : J → R) : eval (c • z) φ = c ^ d * eval z φ := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hφ (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem evalQ_smul {b : MvPolynomial (Ix κ) ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f) (c : ℂ)
    (z : Ix κ → ℂ) :
    eval (c • z) (map (algebraMap ℚ ℂ) b) = c ^ n * eval z (map (algebraMap ℚ ℂ) b) := by
  obtain ⟨f, hf, rfl⟩ := hb
  exact eval_smul_of_homog ((hf.map _).map _) c z

omit [Fintype κ] in

theorem continuous_evalQ (b : MvPolynomial (Ix κ) ℚ) :
    Continuous fun z : Ix κ → ℂ => eval z (map (algebraMap ℚ ℂ) b) :=
  (map (algebraMap ℚ ℂ) b).continuous_eval

theorem pairVal_bound {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) {n : ℕ} {b b' : MvPolynomial (Ix κ) ℚ}
    (hb : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b' = map (Int.castRingHom ℚ) f) :
    Measurable (pairVal m n b b') ∧ ∃ C : ℝ, ∀ z, ‖pairVal m n b b' z‖ ≤ C := by
  set h := pairVal m n b b' with hh
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn
  have hcont : ContinuousOn h {0}ᶜ := by
    refine (((continuous_evalQ b).continuousOn.mul (continuous_evalQ b').continuousOn.star).div
      (Complex.continuous_ofReal.comp_continuousOn (hρ.pow _)) fun z hz => ?_)
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (m.pos z hz).ne')
  have hnorm : ∀ z, ‖h z‖ = ‖eval z (map (algebraMap ℚ ℂ) b)‖ * ‖eval z (map (algebraMap ℚ ℂ) b')‖ / m.ρ z ^ (2 * n) := by
    intro z
    simp only [hh, pairVal, norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (pow_nonneg (m.nonneg z) _)]
  have hsm : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → ‖h (c • z)‖ = ‖h z‖ := by
    intro c z hc
    rw [hnorm, hnorm, evalQ_smul hb, evalQ_smul hb', m.smul]
    have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [norm_mul, norm_mul, norm_pow, mul_pow]
    have e : ‖c‖ ^ n * ‖c‖ ^ n = ‖c‖ ^ (2 * n) := by rw [← pow_add, ← two_mul]
    rw [show ‖c‖ ^ n * ‖eval z (map (algebraMap ℚ ℂ) b)‖ * (‖c‖ ^ n * ‖eval z (map (algebraMap ℚ ℂ) b')‖) =
      (‖c‖ ^ n * ‖c‖ ^ n) * (‖eval z (map (algebraMap ℚ ℂ) b)‖ * ‖eval z (map (algebraMap ℚ ℂ) b')‖) by ring, e,
      mul_div_mul_left _ _ (pow_ne_zero _ hc'.ne')]
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Ix κ → ℂ) 1).exists_bound_of_continuousOn
    (hcont.mono fun z hz => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      simp at hz)
  refine ⟨measurable_of_continuousOn_compl_singleton 0 hcont, max C ‖h 0‖, fun z => ?_⟩
  by_cases hz : z = 0
  · rw [hz]; exact le_max_right _ _
  · have hz' : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
    have hu : ((‖z‖ : ℂ)⁻¹ • z) ∈ Metric.sphere (0 : Ix κ → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
    have : z = (‖z‖ : ℂ) • ((‖z‖ : ℂ)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hz', one_smul]
    rw [this, hsm _ _ hz']
    exact (hC _ hu).trans (le_max_left _ _)

theorem measurable_conjPt : Measurable (conjPt : (Ix κ → ℂ) → Ix κ → ℂ) :=
  (continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)).measurable

end ResChiSymMeasure

open ResChiSymMeasure in

theorem ResChiSymMeasure.full : ResChiSymMeasure.Statement := by
  intro D Ω _ _ κ _ d hf n
  have : IsProbabilityMeasure d.dV := d.vol.1
  have hmult : ∀ w : NumberField.InfinitePlace ℚ, (w.mult : ℝ) = 1 := by
    intro w
    have h1 := NumberField.totalWeight_eq_sum_mult ℚ
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Fintype.sum_unique] at h1
    rw [Subsingleton.elim w default, ← h1, Nat.cast_one]
  have hemb : ∀ w : NumberField.InfinitePlace ℚ, w.embedding = algebraMap ℚ ℂ :=
    fun w => Subsingleton.elim _ _
  have hw : (Height.totalWeight ℚ : ℝ) = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Nat.cast_one]
  have hg : Measurable (conjPt ∘ resPt d) := measurable_conjPt.comp hf
  unfold resChi chi
  by_cases h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2
  swap
  · rw [dif_neg h, dif_neg h]
  rw [dif_pos h, dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r, b⟩ := p
  have hp' : IsSecBasis d.x n b := hp
  have hG : resGram d n b = realGram (K := ℚ) (fun _ => d.m)
      (fun _ => IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV) n b := by
    ext k l
    obtain ⟨hmeas, C, hC⟩ := pairVal_bound d.smooth (hp'.1 k) (hp'.1 l)
    have hint : ∀ φ : d.R.X → Ix κ → ℂ, Measurable φ →
        Integrable (pairVal d.m n (b k) (b l)) (d.dV.map φ) := fun φ _ =>
      Integrable.of_bound hmeas.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    simp only [realGram, hmult, hemb, one_mul, Fintype.sum_unique]
    change _ = (∫ z, pairVal d.m n (b k) (b l) z ∂IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV).re
    rw [IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure, integral_smul_measure,
      integral_add_measure (hint _ hf) (hint _ hg), integral_map hf.aemeasurable hmeas.aestronglyMeasurable,
      integral_map hg.aemeasurable hmeas.aestronglyMeasurable]
    simp only [resGram, Function.comp_apply, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hG]
  simp only [l2Degree, hw, div_one]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
