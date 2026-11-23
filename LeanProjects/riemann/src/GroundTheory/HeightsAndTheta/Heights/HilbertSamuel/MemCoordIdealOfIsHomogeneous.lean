import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.MeasurableResPtHsmProjLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

namespace ResolutionL2SymmetricMeasure

set_option linter.unusedSectionVars false

variable {J : Type} [Fintype J]

theorem coneMap_of_isHomogeneous' {Ω : Type*} [CommRing Ω] [Algebra ℤ Ω] (x : J → Ω) {f : MvPolynomial J ℤ}
    {n : ℕ} (hf : f.IsHomogeneous n) :
    coneMap ℤ x f = Polynomial.C (aeval x f) * Polynomial.X ^ n := by
  simp only [coneMap, aeval_def, eval₂_eq, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = n := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    hdeg, Polynomial.algebraMap_apply, map_mul, mul_assoc]

theorem mem_coordIdeal_of_isHomogeneous' {Ω : Type*} [CommRing Ω] [Algebra ℤ Ω] (x : J → Ω)
    {f : MvPolynomial J ℤ} {n : ℕ} (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal ℤ x := by
  rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous' x hf, h, map_zero, zero_mul]

theorem continuous_conjPt' : Continuous (conjPt : (J → ℂ) → J → ℂ) :=
  continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

theorem eval_conjPt_int (f : MvPolynomial J ℤ) (z : J → ℂ) :
    eval (conjPt z) (map (Int.castRingHom ℂ) f) = conj (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left,
    RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)]
  rfl

theorem measurable_rho (m : ConeMetric ℂ J) (hm : IsSmoothMetric m) : Measurable m.ρ :=
  measurable_of_continuousOn_compl_singleton 0 (hm.continuousOn.mono fun _ hz => hz)

theorem measurable_ptNorm (m : ConeMetric ℂ J) (hm : IsSmoothMetric m) (n : ℕ) (g : MvPolynomial J ℤ) :
    Measurable (ptNorm m (Int.castRingHom ℂ) n g) := by
  unfold ptNorm
  exact ((MvPolynomial.continuous_eval _).measurable.norm).div ((measurable_rho m hm).pow_const n)

theorem ptNorm_conjPt {m : ConeMetric ℂ J} (hm : IsConjInvariant m) (n : ℕ) (g : MvPolynomial J ℤ)
    (z : J → ℂ) : ptNorm m (Int.castRingHom ℂ) n g (conjPt z) = ptNorm m (Int.castRingHom ℂ) n g z := by
  unfold ptNorm
  rw [eval_conjPt_int, Complex.norm_conj, show m.ρ (conjPt z) = m.ρ z from hm z]

theorem ptNorm_eq_of_sub_mem {P : Ideal (MvPolynomial J ℤ)} {f g : MvPolynomial J ℤ} (hfg : f - g ∈ P)
    (m : ConeMetric ℂ J) (n : ℕ) {z : J → ℂ} (hz : ∀ h ∈ P, eval z (map (Int.castRingHom ℂ) h) = 0) :
    ptNorm m (Int.castRingHom ℂ) n f z = ptNorm m (Int.castRingHom ℂ) n g z := by
  have h := hz _ hfg
  rw [map_sub, eval_sub, sub_eq_zero] at h
  unfold ptNorm
  rw [h]

theorem resPt_mem {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (d : HSMDatum D Ω κ)
    (y : d.R.X) : ∀ h ∈ coordIdeal ℤ d.x, eval (resPt d y) (map (Int.castRingHom ℂ) h) = 0 :=
  (d.R.mem y y (d.R.mem_U y)).2

theorem full : ResolutionL2SymmetricMeasure.Statement := by
  intro D Ω _ _ κ _ d hmeas n f hf
  classical
  have hex : ∃ g : MvPolynomial (Ix κ) ℤ, g.IsHomogeneous n ∧ aeval d.x g = aeval d.x f := ⟨f, hf, rfl⟩
  unfold IndefiniteRowSideFullHecke.HilbertSamuel.secNorm
  rw [dif_pos hex]
  obtain ⟨hgh, hgx⟩ := hex.choose_spec
  generalize hex.choose = g at hgh hgx ⊢

  have hfg : f - g ∈ coordIdeal ℤ d.x :=
    mem_coordIdeal_of_isHomogeneous' d.x (hf.sub hgh) (by rw [map_sub, hgx, sub_self])
  unfold resolutionSectionL2Norm l2Norm
  set σ := Int.castRingHom ℂ
  have e1 : ∀ y, ptNorm d.m σ n f (resPt d y) = ptNorm d.m σ n g (resPt d y) := fun y =>
    ptNorm_eq_of_sub_mem hfg d.m n (resPt_mem d y)
  have e2 : ∀ y, ptNorm d.m σ n f (conjPt (resPt d y)) = ptNorm d.m σ n g (resPt d y) := fun y => by
    rw [ptNorm_conjPt d.conjInv, e1]
  congr 1
  simp_rw [e1, e2]
  have hψ : Measurable fun z => ptNorm d.m σ n g z ^ 2 := (measurable_ptNorm d.m d.smooth n g).pow_const 2
  have hA : AEMeasurable (resPt d) d.dV := hmeas.aemeasurable
  have hB : AEMeasurable (conjPt ∘ resPt d) d.dV := (continuous_conjPt'.measurable.comp hmeas).aemeasurable
  have hBψ : ∀ y, ptNorm d.m σ n g ((conjPt ∘ resPt d) y) ^ 2 = ptNorm d.m σ n g (resPt d y) ^ 2 := fun y => by
    rw [Function.comp_apply, ptNorm_conjPt d.conjInv]
  have iA : Integrable (fun z => ptNorm d.m σ n g z ^ 2) (d.dV.map (resPt d)) ↔
      Integrable (fun y => ptNorm d.m σ n g (resPt d y) ^ 2) d.dV :=
    integrable_map_measure hψ.aestronglyMeasurable hA
  have iB : Integrable (fun z => ptNorm d.m σ n g z ^ 2) (d.dV.map (conjPt ∘ resPt d)) ↔
      Integrable (fun y => ptNorm d.m σ n g (resPt d y) ^ 2) d.dV := by
    rw [integrable_map_measure hψ.aestronglyMeasurable hB]
    exact integrable_congr (Filter.Eventually.of_forall hBψ)
  have jA : ∫ z, ptNorm d.m σ n g z ^ 2 ∂(d.dV.map (resPt d)) =
      ∫ y, ptNorm d.m σ n g (resPt d y) ^ 2 ∂d.dV :=
    integral_map hA hψ.aestronglyMeasurable
  have jB : ∫ z, ptNorm d.m σ n g z ^ 2 ∂(d.dV.map (conjPt ∘ resPt d)) =
      ∫ y, ptNorm d.m σ n g (resPt d y) ^ 2 ∂d.dV := by
    rw [integral_map hB hψ.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall hBψ)
  unfold IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure
  rw [integral_smul_measure]
  by_cases hi : Integrable (fun y => ptNorm d.m σ n g (resPt d y) ^ 2) d.dV
  · rw [integral_add_measure (iA.2 hi) (iB.2 hi), jA, jB]
    simp
  · have hn : ¬ Integrable (fun z => ptNorm d.m σ n g z ^ 2) (d.dV.map (resPt d) + d.dV.map (conjPt ∘ resPt d)) := by
      rw [integrable_add_measure]
      exact fun h => hi (iA.1 h.1)
    rw [integral_undef hn, integral_undef hi]
    simp

end ResolutionL2SymmetricMeasure

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
