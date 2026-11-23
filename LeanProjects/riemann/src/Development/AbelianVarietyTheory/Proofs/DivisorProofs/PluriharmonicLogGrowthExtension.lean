import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPoissonPuncturedDiscStatement
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff

namespace GlobalTheory

theorem fderiv_fderiv_comp_affine_of_contDiffOn {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (a : E) (L : ℂ →L[ℝ] E) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (ζ : ℂ) (hζ : a + L ζ ∈ U) (u v : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => f (a + L y))) ζ u v =
      fderiv ℝ (fderiv ℝ f) (a + L ζ) (L u) (L v) := by
  have hA : ∀ y, HasFDerivAt (fun y : ℂ => a + L y) L y := fun y => by
    simpa using (L.hasFDerivAt (x := y)).const_add a
  have hV : IsOpen {y : ℂ | a + L y ∈ U} := hU.preimage (by fun_prop)
  have hev : fderiv ℝ (fun y => f (a + L y)) =ᶠ[𝓝 ζ] fun y => (fderiv ℝ f (a + L y)).comp L := by
    filter_upwards [hV.mem_nhds hζ] with y hy
    have hfd : DifferentiableAt ℝ f (a + L y) :=
      (hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    exact (hfd.hasFDerivAt.comp y (hA y)).fderiv
  rw [hev.fderiv_eq]
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) (a + L ζ) := by
    have := (hf.contDiffAt (hU.mem_nhds hζ)).fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)
    exact this.differentiableAt one_ne_zero
  have hT : HasFDerivAt (fun y => (fderiv ℝ f (a + L y)).comp L)
      (((ContinuousLinearMap.compL ℝ ℂ E ℝ).flip L).comp
        ((fderiv ℝ (fderiv ℝ f) (a + L ζ)).comp L)) ζ := by
    have h1 := hf2.hasFDerivAt.comp ζ (hA ζ)
    exact ((ContinuousLinearMap.compL ℝ ℂ E ℝ).flip L).hasFDerivAt.comp ζ h1
  rw [hT.fderiv]
  simp

theorem poissonInt_update_eq_of_levi_flat : ∀ (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (R r : ℝ) (f : (Fin e → ℂ) → ℝ), 0 < r → r < R → R ≤ 1 → c i = 0 → i ∉ S → ContDiffOn ℝ ∞ f {z | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0} → (∀ z ∈ Metric.ball c R, (∀ k ∈ insert i S, z k ≠ 0) → ∀ w, levi f z w = 0) → (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z ∈ Metric.ball c R, (∀ k ∈ insert i S, z k ≠ 0) → |f z| ≤ K - ε * ∑ k ∈ insert i S, Real.log ‖z k‖) → ∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → ReciprocityTheory.AnForm.A.poissonInt (fun ζ => f (Function.update z i ζ)) r (z i) = f z := by
  intro e S i c R r f hr hrR hR1 hci hiS hf hlevi hgrow z hz hzS hzi
  set U : Set (Fin e → ℂ) := {z | z ∈ Metric.ball c R ∧ ∀ k ∈ insert i S, z k ≠ 0} with hUdef
  have hUo : IsOpen U := by
    have hU' : U = Metric.ball c R ∩ ⋂ k ∈ insert i S, {z : Fin e → ℂ | z k ≠ 0} := by
      ext y; simp [U]
    rw [hU']
    exact isOpen_ball.inter (isOpen_biInter_finset fun k _ =>
      isOpen_compl_singleton.preimage (continuous_apply k))
  let L : ℂ →L[ℝ] (Fin e → ℂ) := ContinuousLinearMap.single ℝ (fun _ : Fin e => ℂ) i
  set a : Fin e → ℂ := Function.update z i 0 with ha
  have hA : ∀ ζ, Function.update z i ζ = a + L ζ := by
    intro ζ; funext k
    by_cases hk : k = i
    · rw [hk]; simp [a, L]
    · simp [a, L, hk]
  have hmem : ∀ ζ : ℂ, ‖ζ‖ < R → ζ ≠ 0 → a + L ζ ∈ U := by
    intro ζ hζR hζ0
    rw [← hA]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_pi_lt_iff (by linarith)]
      intro k
      by_cases hk : k = i
      · rw [hk]; simpa [hci] using hζR
      · rw [Function.update_of_ne hk]
        exact (dist_le_pi_dist z c k).trans_lt ((Metric.mem_ball.1 hz).trans hrR)
    · intro k hk
      rcases Finset.mem_insert.1 hk with hk | hk
      · rw [hk]; simpa using hζ0
      · have hki : k ≠ i := fun h => hiS (h ▸ hk)
        rw [Function.update_of_ne hki]; exact hzS k hk
  have hnorm : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, ‖ζ‖ < R := by
    intro ζ hζ
    have := Metric.mem_closedBall.1 hζ
    rw [dist_zero_right] at this; linarith
  set h : ℂ → ℝ := fun ζ => f (Function.update z i ζ) with hhdef
  have hh' : h = fun y => f (a + L y) := by funext y; simp only [h, hA]
  have hV : IsOpen {y : ℂ | a + L y ∈ U} := hUo.preimage (by fun_prop)
  have hharm : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall 0 r \ {0}) := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := hζ.2
    have hm := hmem ζ (hnorm ζ hζ.1) hζ0
    rw [hh']
    refine ⟨?_, ?_⟩
    · have h1 : ContDiffAt ℝ 2 f (a + L ζ) :=
        (hf.contDiffAt (hUo.mem_nhds hm)).of_le (by first | exact WithTop.coe_le_coe.2 le_top | decide | exact_mod_cast le_top)
      exact h1.comp ζ (by fun_prop)
    · filter_upwards [hV.mem_nhds hm] with y hy
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
      simp only [iteratedFDeriv_two_apply, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      rw [fderiv_fderiv_comp_affine_of_contDiffOn f a L U hUo hf y hy,
        fderiv_fderiv_comp_affine_of_contDiffOn f a L U hUo hf y hy]
      have hl := hlevi (a + L y) hy.1 hy.2 (L 1)
      have hLI : L Complex.I = Complex.I • L 1 := by
        funext k; by_cases hk : k = i <;> simp [L, hk]
      rw [hLI]; unfold levi at hl; linarith
  have hgrow' : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, ζ ≠ 0 →
      |h ζ| ≤ K - ε * Real.log ‖ζ‖ := by
    intro ε hε
    obtain ⟨K, hK⟩ := hgrow ε hε
    refine ⟨K - ε * ∑ k ∈ S, Real.log ‖z k‖, fun ζ hζ hζ0 => ?_⟩
    have hm := hmem ζ (hnorm ζ hζ) hζ0
    rw [← hA] at hm
    have hb := hK _ hm.1 hm.2
    rw [Finset.sum_insert hiS, Function.update_self] at hb
    have hs : ∑ k ∈ S, Real.log ‖Function.update z i ζ k‖ = ∑ k ∈ S, Real.log ‖z k‖ :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (fun hki : k = i => hiS (hki ▸ hk))]
    rw [hs, mul_add] at hb
    simp only [h]; linarith
  have hw : z i ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball]
    have := (dist_le_pi_dist z c i).trans_lt (Metric.mem_ball.1 hz)
    rwa [hci] at this
  have key := GlobalTheory.T.harmonic_poisson_punctured_disc r h hr (hrR.le.trans hR1) hharm hgrow' (z i) hw hzi
  rw [← key]
  simp [h]

end GlobalTheory
