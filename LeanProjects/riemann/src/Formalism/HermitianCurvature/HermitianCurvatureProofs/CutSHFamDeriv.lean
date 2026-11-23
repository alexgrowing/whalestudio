import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

open MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.CutSH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_derivative : CutSH.FamDeriv := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG v
  obtain ⟨hloc, hsupp⟩ := hG
  refine ⟨?_, ?_⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hGf⟩ := hloc t₀ ht₀ γ₀ hγ₀
    refine ⟨U, fun p => fderiv ℝ f p ((v, 0) : ℂ × B.Mat P.k (P.r - (j + 1))), hU, hmem, ?_, ?_⟩
    · exact (hf.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
    · rintro ⟨t, γ⟩ hp hγ
      simp only [famP, Set.indicator_of_mem hγ]
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun u => f (u, γ) := by
        have hc : Continuous fun u : ℂ => (u, γ) := continuous_id.prodMk continuous_const
        have : ∀ᶠ u in 𝓝 t, (u, γ) ∈ U := hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
        filter_upwards [this] with u hu
        exact hGf (u, γ) hu hγ
      rw [hev.fderiv_eq]
      have hfd : DifferentiableAt ℝ f (t, γ) :=
        (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
      have hin := hasFDerivAt_prodMk_left (𝕜 := ℝ) t γ
      rw [show (fun u : ℂ => f (u, γ)) = f ∘ fun u => (u, γ) from rfl, (hfd.hasFDerivAt.comp t hin).fderiv]
      rfl
  · intro K hK hK0
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_compl_singleton (x := (0 : ℂ)))
      (fun t ht => by simpa using hK0 t ht)
    obtain ⟨C, hC, ε, hε, hCε⟩ := hsupp (Metric.cthickening δ K) hK.cthickening
      (fun t ht => by simpa using hsub ht)
    refine ⟨C, hC, ε, hε, fun t ht γ hne => ?_⟩
    have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := by
      by_contra h
      exact hne (by simp [famP, Set.indicator_of_notMem h])
    have hd : fderiv ℝ (fun u : ℂ => G u γ) t v ≠ 0 := by
      simpa [famP, Set.indicator_of_mem hγ] using hne
    have hex : ∃ u ∈ Metric.ball t δ, G u γ ≠ 0 := by
      by_contra hno
      push Not at hno
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds t hδ] with u hu using hno u hu
      exact hd (by rw [hev.fderiv_eq]; simp)
    obtain ⟨u, hu, hGu⟩ := hex
    have huK : u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le u t δ K ht (le_of_lt (Metric.mem_ball.mp hu))
    obtain ⟨hγC, hε'⟩ := hCε u huK γ hGu
    exact ⟨hγC, fun _ => hε' hγ⟩

end Formalism.FourierDecayAlt.P
