import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCoordsOfLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyGrowthSpreadOfIntegralMonodromyStatement
open Filter Topology

namespace GlobalTheory.StripGrowth

theorem int_coord_const (g m : ℕ) (U : Set ℂ) (hU : IsPreconnected U) (μ ν : ℂ → Fin m → Fin g → ℂ)
    (hμ : ContinuousOn μ U) (hν : ContinuousOn ν U) (hli : ∀ s ∈ U, LinearIndependent ℝ (μ s))
    (hn : ∀ s ∈ U, ∀ j, ∃ n : Fin m → ℤ, ν s j = ∑ i, n i • μ s i) :
    ∃ P : Fin m → Fin m → ℤ, ∀ s ∈ U, ∀ j, ν s j = ∑ i, P j i • μ s i := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨0, by simp⟩
  choose! n hnE using hn
  have key : ∀ j, ∀ s ∈ U, n s j = n s₀ j := by
    intro j
    have hcont : ContinuousOn (fun s i => ((n s j i : ℤ) : ℝ)) U := by
      refine GlobalTheory.T.continuousOn_coords_of_linearIndependent' g m U μ (fun s => ν s j) (fun s i => (n s j i : ℝ)) hμ ?_ hli ?_
      · exact (continuous_apply j).comp_continuousOn hν
      · intro s hs
        rw [hnE s hs j]
        simp [Int.cast_smul_eq_zsmul]
    have hcz : ContinuousOn (fun s => n s j) U := by
      rw [continuousOn_pi] at hcont ⊢
      intro i
      exact (Int.isUniformEmbedding_coe_real.isEmbedding.continuousOn_iff).2 (hcont i)
    intro s hs
    exact hU.constant hcz hs hs₀
  exact ⟨n s₀, fun s hs j => by rw [hnE s hs j, key j s hs]⟩

theorem strip_growth : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ), ContinuousOn lam {s : ℂ | s.re < 0} → (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lam s)) → (∀ s : ℂ, s.re < 0 → ∀ z : Fin g → ℂ, (∃ n : Fin m → ℤ, z = ∑ j, n j • lam (s + 2 * Real.pi * Complex.I) j) ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam s j) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  intro g m lam C k hcont hli hspan hB
  have hU : IsPreconnected {s : ℂ | s.re < 0} := (convex_halfSpace_re_lt 0).isPreconnected
  have hre : ∀ s : ℂ, (s + 2 * Real.pi * Complex.I).re = s.re := by intro s; simp
  have hshift : ContinuousOn (fun s => lam (s + 2 * Real.pi * Complex.I)) {s : ℂ | s.re < 0} :=
    hcont.comp (continuousOn_id.add continuousOn_const) (fun s hs => by
      simpa [Set.mem_setOf_eq, hre] using hs)
  have hli' : ∀ s ∈ {s : ℂ | s.re < 0}, LinearIndependent ℝ (lam (s + 2 * Real.pi * Complex.I)) :=
    fun s hs => hli _ (by simpa [hre] using hs)
  have hsingle : ∀ (v : Fin m → Fin g → ℂ) (j : Fin m), v j = ∑ i, (Pi.single j 1 : Fin m → ℤ) i • v i := by
    intro v j
    classical
    simp [Pi.single_apply]
  obtain ⟨P, hP⟩ := int_coord_const g m _ hU lam (fun s => lam (s + 2 * Real.pi * Complex.I)) hcont hshift
    (fun s hs => hli s hs) (fun s hs j => (hspan s hs _).1 ⟨Pi.single j 1, hsingle _ j⟩)
  obtain ⟨Q, hQ⟩ := int_coord_const g m _ hU (fun s => lam (s + 2 * Real.pi * Complex.I)) lam hshift hcont
    hli' (fun s hs j => (hspan s hs _).2 ⟨Pi.single j 1, hsingle _ j⟩)
  exact GlobalTheory.T.polyGrowth_strip_of_integral_monodromy g m lam C k P Q (fun s hs j => hP s hs j) (fun s hs j => hQ s hs j) hB

end GlobalTheory.StripGrowth
