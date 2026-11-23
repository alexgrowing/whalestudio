import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalyticStatement

noncomputable section

namespace RootFieldNumerics.Bh

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo

theorem contAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X} {f : X → ℂ}
    (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
    show (A.chart j).symm (A.chart j x) ∈ U
    rwa [(A.chart j).left_inv hj]⟩).continuousAt
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem surj_of_degree {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [CompactSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S : Set X} (hc : Continuous h) (hd : IsDegreeOff A B h 1 S) :
    Function.Surjective h := by
  have h1 : IsClosed (Set.range h) := (isCompact_range hc).isClosed
  have h2 : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.1
  have h3 : Sᶜ ⊆ Set.range h := fun x hx => by
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (s := h ⁻¹' {x}) (by rw [hd.2.2.2.2.1 x hx]; exact one_ne_zero)
    exact ⟨y, hy⟩
  rw [← Set.range_eq_univ, ← h1.closure_eq]
  exact (h2.mono h3).closure_eq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SO_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => by rw [inv_mul_cancel_left₀ (hc _)]⟩

theorem SO_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => (mul_assoc _ _ _).symm⟩

theorem SO_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) : z q ≠ 0 ↔ z' q ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  simp [hc q.1]

theorem isOpen_lift_ne {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (q : Σ k, ι k) :
    IsOpen {w : R.X | R.lift w w q ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun w hw => ?_
  filter_upwards [(R.isOpen_U w).mem_nhds (R.mem_U w),
    (contAt_of_holoOn (R.holo w q) (R.mem_U w)).eventually_ne hw] with w' h1 h2
  exact (SO_ne (R.compat w' w w' ⟨R.mem_U w', h1⟩) q).2 h2

theorem exists_inverse {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (hJ : J = ⊤) {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (π : R.X → X) (hs : Function.Surjective π)
    (key : ∀ w₁, ∃ (O : Set X) (μ : X → (Σ k, ι k) → ℂ), IsOpen O ∧ π w₁ ∈ O ∧ (∀ q, A.HoloOn O fun x => μ x q) ∧
      ∀ w, π w ∈ O → SameOrbit (R.lift w w) (μ (π w))) :
    ∃ ψ : X → R.X, HoloMap A R.A ψ ∧ (∀ x, π (ψ x) = x) ∧ ∀ w, ψ (π w) = w := by
  have hinj : Function.Injective π := fun w w₁ e₀ => by
    obtain ⟨O, μ, -, h1, -, h2⟩ := key w₁
    have a1 := h2 w (e₀ ▸ h1)
    rw [e₀] at a1
    refine R.inj w w₁ (fun h => ?_) (SO_trans a1 (SO_symm (h2 w₁ h1)))
    simpa using h.2 1 (hJ ▸ Submodule.mem_top)
  let ψ := Function.surjInv hs
  have r : ∀ x, π (ψ x) = x := Function.surjInv_eq hs
  have loc : ∀ j, ∀ t ∈ (A.chart j).target, ∃ V, IsOpen V ∧ t ∈ V ∧ ContinuousOn (ψ ∘ (A.chart j).symm) V ∧
      ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ (ψ ∘ (A.chart j).symm)) (V ∩ (ψ ∘ (A.chart j).symm) ⁻¹' (R.A.chart k).source) := by
    intro j t ht
    obtain ⟨O, μ, hO, h1, h2, h3⟩ := key (ψ ((A.chart j).symm t))
    rw [r] at h1
    have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O) := (A.chart j).isOpen_inter_preimage_symm hO
    refine ⟨_, hV, ⟨ht, h1⟩, GlobalTheory.T.lift_to_log_resolution_analytic K ι P J e e R hJ _ (fun u => μ ((A.chart j).symm u)) _ hV (fun q => h2 q j)
      fun u hu => ?_⟩
    have := h3 (ψ ((A.chart j).symm u)) (by rw [r]; exact hu.2)
    rwa [r] at this
  refine ⟨ψ, ⟨continuous_iff_continuousAt.2 fun x => ?_, fun j k t ht => ?_⟩, r, fun w => hinj (r _)⟩
  · obtain ⟨j, hj⟩ := A.cover x
    obtain ⟨V, hV, h1, h2, -⟩ := loc j _ ((A.chart j).map_source hj)
    refine ((h2.continuousAt (hV.mem_nhds h1)).comp ((A.chart j).continuousAt hj)).congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  · obtain ⟨V, -, h1, -, h2⟩ := loc j t ht.1
    exact h2 k t ⟨h1, ht.2⟩

end RootFieldNumerics.Bh
