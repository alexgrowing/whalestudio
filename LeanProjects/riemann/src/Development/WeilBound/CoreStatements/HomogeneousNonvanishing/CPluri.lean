import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

namespace PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts

open ReciprocityTheory.AnForm Filter Topology Set Metric Complex

theorem exists_re_of_levi_zero {e : ℕ} {d : (Fin e → ℂ) → ℝ} {c : Fin e → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ContDiffOn ℝ 2 d (ball c r)) (h0 : ∀ z ∈ ball c r, ∀ w, levi d z w = 0) :
    ∃ G : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G (ball c r) ∧ ∀ z ∈ ball c r, d z = (G z).re := by
  have hUo : IsOpen (ball c r) := isOpen_ball
  let J : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) := Complex.I • ContinuousLinearMap.id ℝ (Fin e → ℂ)
  let P : ((Fin e → ℂ) →L[ℝ] ℝ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) (Fin e → ℂ) ℝ).flip J
  have hP : ∀ (L : (Fin e → ℂ) →L[ℝ] ℝ) (w : Fin e → ℂ), P L w = L (Complex.I • w) := fun L w => rfl
  let ω : (Fin e → ℂ) → (Fin e → ℂ) →L[ℝ] ℝ := fun z => -P (fderiv ℝ d z)
  have hC : ∀ a ∈ ball c r, ContDiffAt ℝ 2 d a := fun a ha => hd.contDiffAt (hUo.mem_nhds ha)
  have hω : ∀ a ∈ ball c r, HasFDerivAt ω (-(P.comp (fderiv ℝ (fderiv ℝ d) a))) a := by
    intro a ha
    have h1 : HasFDerivAt (fderiv ℝ d) (fderiv ℝ (fderiv ℝ d) a) a :=
      (((hC a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    exact (P.hasFDerivAt.comp a h1).neg
  have hωd : DifferentiableOn ℝ ω (ball c r) := fun a ha =>
    (hω a ha).differentiableAt.differentiableWithinAt
  have hsymm : ∀ a ∈ ball c r, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x := by
    intro a ha x y
    rw [(hω a ha).fderiv]
    have hS : IsSymmSndFDerivAt ℝ d a := (hC a ha).isSymmSndFDerivAt (by simp)
    have hL : ∀ w, fderiv ℝ (fderiv ℝ d) a w w
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • w) (Complex.I • w) = 0 := by
      intro w
      have h := h0 a ha w
      simp only [levi] at h
      linarith
    have hB : ∀ u v, fderiv ℝ (fderiv ℝ d) a u v
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • u) (Complex.I • v) = 0 := by
      intro u v
      have h1 := hL (u + v)
      have h2 := hL u
      have h3 := hL v
      simp only [smul_add, map_add, ContinuousLinearMap.add_apply] at h1
      have e1 := hS u v
      have e2 := hS (Complex.I • u) (Complex.I • v)
      linarith
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, hP]
    have k1 := hB x (Complex.I • y)
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at k1
    have k2 := hS (Complex.I • x) y
    linarith
  obtain ⟨v, hv⟩ := (convex_ball c r).exists_forall_hasFDerivAt_of_fderiv_symmetric hUo hωd hsymm
  refine ⟨fun z => (d z : ℂ) + (v z : ℂ) * Complex.I, ?_, ?_⟩
  · have hO := ReciprocityTheory.AnForm.Osgood.osgood
    unfold ReciprocityTheory.AnForm.Osgood.OsgoodStatement at hO
    apply hO e _ _ hUo
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hdz : HasFDerivAt d (fderiv ℝ d z) z :=
      ((hC z hz).differentiableAt (by norm_num)).hasFDerivAt
    have hG : HasFDerivAt (fun z => (d z : ℂ) + (v z : ℂ) * Complex.I)
        (Complex.ofRealCLM.comp (fderiv ℝ d z) + Complex.I • Complex.ofRealCLM.comp (ω z)) z :=
      (Complex.ofRealCLM.hasFDerivAt.comp z hdz).add
        ((Complex.ofRealCLM.hasFDerivAt.comp z (hv z hz)).mul_const Complex.I)
    rw [differentiableAt_iff_restrictScalars ℝ hG.differentiableAt]
    refine ⟨StrongDual.extendRCLike (fderiv ℝ d z), ?_⟩
    rw [hG.fderiv]
    ext w
    simp [StrongDual.extendRCLike_apply, ω, hP]
    ring
  · intro z _
    simp

end PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts
