import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem finiteDim_norm_le_on_Icc_of_determined :
    ∀ (V : Submodule ℂ (ℝ → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, Continuous f) → ∀ ℓ : ℝ, 0 < ℓ →
    (∀ f ∈ V, (∀ x ∈ Set.Icc 0 ℓ, f x = 0) → f = 0) → ∀ R : ℝ, ∃ C : ℝ, ∀ f ∈ V, ∀ M : ℝ,
      (∀ x ∈ Set.Icc 0 ℓ, ‖f x‖ ≤ M) → ∀ t ∈ Set.Icc (-R) R, ‖f t‖ ≤ C * M := by
  intro V hV hcont ℓ hℓ hdet R
  let ev : Set.Icc (0:ℝ) ℓ → Module.Dual ℂ V := fun x =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : ℝ => ℂ) (x:ℝ)).comp V.subtype
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ ev
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  classical
  let T : V →ₗ[ℂ] (κ → ℂ) := LinearMap.pi (fun k => ev (a k))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h1 : Submodule.span ℂ (Set.range (ev ∘ a)) ≤ LinearMap.ker (Module.Dual.eval ℂ V g) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := congrFun hg k
      simpa [T] using this
    rw [hspan] at h1
    have h2 : ∀ x ∈ Set.Icc (0:ℝ) ℓ, (g : ℝ → ℂ) x = 0 := by
      intro x hx
      have := h1 (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
      simpa [ev] using this
    exact Subtype.ext (hdet g g.2 h2)
  obtain ⟨S, hS⟩ := LinearMap.exists_leftInverse_of_injective T hT
  let g : κ → ℝ → ℂ := fun k => (S (Pi.single k 1) : ℝ → ℂ)
  have hB : ∀ k, ∃ B, ∀ t ∈ Set.Icc (-R) R, ‖g k t‖ ≤ B := fun k =>
    (isCompact_Icc).exists_bound_of_continuousOn (hcont _ (S (Pi.single k 1)).2).continuousOn
  choose B hB using hB
  refine ⟨∑ k, max (B k) 0, ?_⟩
  intro f hf M hM t ht
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hℓ.le⟩)
  have e : (⟨f, hf⟩ : V) = S (T ⟨f, hf⟩) := (LinearMap.congr_fun hS _).symm
  have e2 : T ⟨f, hf⟩ = ∑ k, (f (a k)) • (Pi.single k 1 : κ → ℂ) := by
    ext j; simp [T, ev, Finset.sum_apply, Pi.single_apply]
  rw [e2, map_sum] at e
  have e3 := congrFun (congrArg Subtype.val e) t
  have hft : f t = ∑ k, f (a k) * g k t := by
    simpa [g, Finset.sum_apply] using e3
  rw [hft, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hB k t ht).trans (le_max_left _ _)) (hM _ (a k).2) (norm_nonneg _)
    (le_max_right _ _)

end GlobalTheory
