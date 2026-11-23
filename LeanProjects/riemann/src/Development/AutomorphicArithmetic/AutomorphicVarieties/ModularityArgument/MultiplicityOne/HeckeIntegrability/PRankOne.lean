import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt

namespace UpperTheory.V.Z.Mult.Pi

private lemma trace_idem {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (f : Module.End ℂ Y) (hf : f * f = f) (hx : ∀ x, ∃ c : ℂ, f * x * f = c • f) (h0 : f ≠ 0) :
    LinearMap.trace ℂ Y f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (LinearMap.ext h)
  have hidem : ∀ v, f (f v) = f v := fun v => by
    have := congrArg (fun g : Module.End ℂ Y => g v) hf
    simpa [Module.End.mul_apply] using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ (f y) = 1 := by
    have h1 : ¬ ∀ φ : Module.Dual ℂ Y, φ (f y) = 0 := fun h =>
      hy ((Module.forall_dual_apply_eq_zero_iff ℂ (f y)).1 h)
    push_neg at h1
    obtain ⟨ψ, hψ⟩ := h1
    refine ⟨(ψ (f y))⁻¹ • ψ, ?_⟩
    simp [hψ]
  have hr : LinearMap.range f = Submodule.span ℂ {f y} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := hx (φ.smulRight v)
      have h2 := congrArg (fun g : Module.End ℂ Y => g (f y)) hc
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, hidem, hφ,
        map_smul, one_smul] at h2
      exact Submodule.mem_span_singleton.2 ⟨c, h2.symm⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨y, rfl⟩
  have hp : LinearMap.IsProj (LinearMap.range f) f :=
    ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hidem v⟩
  rw [hp.trace, hr, finrank_span_singleton hy]
  simp

theorem rankOne_pf : RankOne := by
  intro Y _ _ _ f A hf hA hc hx
  by_cases h0 : f = 0
  · left
    simp [h0]
  right
  obtain ⟨c, hcA⟩ := hx A
  have hfA : f * A = c • f := by
    calc f * A = f * f * A := by rw [hf]
      _ = f * (f * A) := mul_assoc _ _ _
      _ = f * (A * f) := by rw [hc]
      _ = f * A * f := (mul_assoc _ _ _).symm
      _ = c • f := hcA
  have hsq : (c * c) • f = f := by
    calc (c * c) • f = (c • f) * (c • f) := by rw [smul_mul_smul_comm, hf]
      _ = (f * A) * (f * A) := by rw [hfA]
      _ = f * (A * f) * A := by simp only [mul_assoc]
      _ = f * (f * A) * A := by rw [hc]
      _ = (f * f) * (A * A) := by simp only [mul_assoc]
      _ = f := by rw [hf, hA, mul_one]
  have hcc : c * c = 1 := by
    have h3 : (c * c - 1) • f = 0 := by rw [sub_smul, one_smul, hsq, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h0
  have hn : ‖c‖ = 1 := by
    have h4 : ‖c‖ * ‖c‖ = 1 := by rw [← norm_mul, hcc, norm_one]
    nlinarith [norm_nonneg c, sq_nonneg (‖c‖ - 1)]
  rw [hfA, map_smul, trace_idem f hf hx h0, smul_eq_mul, mul_one, hn]

end UpperTheory.V.Z.Mult.Pi
