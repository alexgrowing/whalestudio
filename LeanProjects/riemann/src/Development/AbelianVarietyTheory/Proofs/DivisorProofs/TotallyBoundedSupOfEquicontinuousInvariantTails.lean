import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem totallyBounded_sup_of_equicontinuous_tails
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G)
    (Φ : Set (G → ℂ))
    (hinv : ∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g)
    (hbd : ∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1)
    (heq : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B →
      ‖φ (g * u) - φ g‖ ≤ ε)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧
      ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  classical
  intro ε hε
  have hδpos : 0 < ε / 4 := by positivity
  obtain ⟨U, hU, hUeq⟩ := heq (ε / 4) hδpos
  obtain ⟨C, hCc, hCB, hCt⟩ := htail (ε / 4) hδpos
  obtain ⟨t, htC, hCcov⟩ := hCc.elim_nhds_subcover (fun x => (fun h => x⁻¹ * h) ⁻¹' U) (by
    intro x _
    have hc : Continuous (fun h : G => x⁻¹ * h) := continuous_const.mul continuous_id
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hU)
  let T : (G → ℂ) → (t → ℂ) := fun φ i => φ i
  have hTb : T '' Φ ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    exact hbd φ hφ i (hCB (htC i i.2))
  have htb : TotallyBounded (T '' Φ) :=
    ((isCompact_closedBall (0 : t → ℂ) 1).totallyBounded).subset hTb
  obtain ⟨s, hsT, hsf, hscov⟩ := Metric.finite_approx_of_totallyBounded htb (ε / 4) hδpos
  let c : (t → ℂ) → (G → ℂ) := fun y => if h : ∃ φ ∈ Φ, T φ = y then h.choose else 0
  have hc : ∀ y ∈ s, c y ∈ Φ ∧ T (c y) = y := by
    intro y hy
    have h : ∃ φ ∈ Φ, T φ = y := hsT hy
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨hsf.toFinset.image c, fun φ hφ => ?_⟩
  obtain ⟨y, hy, hdist⟩ : ∃ y ∈ s, dist (T φ) y < ε / 4 := by
    have := hscov ⟨φ, hφ, rfl⟩
    simpa using this
  obtain ⟨hψ, hTψ⟩ := hc y hy
  refine ⟨c y, Finset.mem_image.2 ⟨y, hsf.mem_toFinset.2 hy, rfl⟩, fun g hg => ?_⟩
  rcases hCt g hg with ⟨s', hs', hsg⟩ | hsmall
  · obtain ⟨x, hxt, hxU⟩ : ∃ x ∈ t, x⁻¹ * (s' * g) ∈ U := by
      have := hCcov hsg
      simpa using this
    have hxB : x ∈ B := hCB (htC x hxt)
    have hmul : x * (x⁻¹ * (s' * g)) = s' * g := mul_inv_cancel_left x _
    have hsgB : s' * g ∈ B := hCB hsg
    have h1 := hUeq φ hφ x hxB _ hxU (by rw [hmul]; exact hsgB)
    have h2 := hUeq (c y) hψ x hxB _ hxU (by rw [hmul]; exact hsgB)
    rw [hmul] at h1 h2
    have h3 : ‖φ x - c y x‖ ≤ ε / 4 := by
      calc ‖φ x - c y x‖ = dist (T φ ⟨x, hxt⟩) (T (c y) ⟨x, hxt⟩) := (dist_eq_norm _ _).symm
        _ ≤ dist (T φ) (T (c y)) := dist_le_pi_dist _ _ _
        _ = dist (T φ) y := by rw [hTψ]
        _ ≤ ε / 4 := hdist.le
    rw [← hinv φ hφ s' hs' g, ← hinv (c y) hψ s' hs' g]
    calc ‖φ (s' * g) - c y (s' * g)‖
        = ‖(φ (s' * g) - φ x) + (φ x - c y x) - (c y (s' * g) - c y x)‖ := by congr 1; ring
      _ ≤ ‖φ (s' * g) - φ x‖ + ‖φ x - c y x‖ + ‖c y (s' * g) - c y x‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ ≤ ε := by linarith
  · exact (norm_sub_le _ _).trans (by linarith [hsmall φ hφ, hsmall (c y) hψ])

end GlobalTheory
