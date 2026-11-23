import Mathlib

theorem UpperTheory.Reformulated.B.GradedPowerSeriesLemmas.char_real :
    ∀ (f : ℝ → ℂ),
    Continuous f →
      (∀ (s t : ℝ), f (s + t) = f s * f t) →
        (∀ (s : ℝ), ‖f s‖ = (1 : ℝ)) → ∃ (b : ℝ), ∀ (s : ℝ), f s = Complex.exp ((↑(b * s) : ℂ) * Complex.I) := by
  intro f hf hadd hn
  have hmem : ∀ s, f s ∈ Submonoid.unitSphere ℂ := fun s => by
    simpa [Submonoid.unitSphere] using hn s
  let F : C(ℝ, Circle) := ⟨fun s => ⟨f s, hmem s⟩, hf.subtype_mk hmem⟩
  have hF : ∀ s, ((F s : Circle) : ℂ) = f s := fun s => rfl
  have hFadd : ∀ s t, F (s + t) = F s * F t := fun s t => by
    apply Circle.ext
    rw [Circle.coe_mul, hF, hF, hF, hadd]
  have hF0 : F 0 = 1 := by
    have h := hFadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := F 0) (by rw [← h, mul_one])
  obtain ⟨g, ⟨hg0, hg⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0 0 (by rw [hF0, Circle.exp_zero])
  have hg' : ∀ s, Circle.exp (g s) = F s := fun s => congrFun hg s
  have hgadd : ∀ s t, g (s + t) = g s + g t := by
    intro s
    have h : (fun t => g (s + t)) = fun t => g s + g t := by
      refine Circle.isCoveringMap_exp.eq_of_comp_eq (by fun_prop) (by fun_prop) ?_ 0 ?_
      · funext t
        simp only [Function.comp_apply, Circle.exp_add, hg', hFadd]
      · simp [hg0]
    exact fun t => congrFun h t
  let G : ℝ →+ ℝ := AddMonoidHom.mk' g hgadd
  refine ⟨g 1, fun s => ?_⟩
  have hlin : g s = g 1 * s := by
    have h := map_real_smul G g.continuous s 1
    have h' : g (s • (1 : ℝ)) = s • g 1 := h
    rw [smul_eq_mul, smul_eq_mul, mul_one] at h'
    rw [h', mul_comm]
  rw [← hF, ← hg', Circle.coe_exp, ← hlin]
