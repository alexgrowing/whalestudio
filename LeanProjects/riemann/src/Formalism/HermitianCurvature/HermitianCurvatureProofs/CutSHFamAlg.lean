import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_algebraic : FamAlg := by
  intro Wp Wq _ _ _ _ _ _ P T j G G' hG hG' m hm
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨hG1', hG2'⟩ := hG'
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    obtain ⟨U', f', hU', hmem', hf', hfe'⟩ := hG1' t₀ ht₀ γ₀ hγ₀
    refine ⟨U ∩ U', fun p => f p + f' p, hU.inter hU', ⟨hmem, hmem'⟩,
      (hf.mono Set.inter_subset_left).add (hf'.mono Set.inter_subset_right), ?_⟩
    intro p hp hpG
    simp only [hfe p hp.1 hpG, hfe' p hp.2 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    obtain ⟨C', hC', ε', hε', hCε'⟩ := hG2' K hK hK0
    refine ⟨C ∪ C', hC.union hC', min ε ε', lt_min hε hε', ?_⟩
    intro t ht γ hne
    by_cases h0 : G t γ = 0
    · have h1 : G' t γ ≠ 0 := by
        intro h1; apply hne; simp [h0, h1]
      obtain ⟨hγ, hb⟩ := hCε' t ht γ h1
      exact ⟨Or.inr hγ, fun hg => (min_le_right _ _).trans (hb hg)⟩
    · obtain ⟨hγ, hb⟩ := hCε t ht γ h0
      exact ⟨Or.inl hγ, fun hg => (min_le_left _ _).trans (hb hg)⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    have hO : IsOpen {p : ℂ × B.Mat P.k (P.r - (j + 1)) | p.1 ≠ 0} :=
      isOpen_ne_fun continuous_fst continuous_const
    refine ⟨U ∩ {p | p.1 ≠ 0}, fun p => m p.1 • f p, hU.inter hO, ⟨hmem, ht₀⟩, ?_, ?_⟩
    · have hm' : ContDiffOn ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) => m p.1) (U ∩ {p | p.1 ≠ 0}) :=
        hm.comp contDiffOn_fst (fun p hp => hp.2)
      exact hm'.smul (hf.mono Set.inter_subset_left)
    · intro p hp hpG
      simp only [hfe p hp.1 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    exact ⟨C, hC, ε, hε, fun t ht γ hne => hCε t ht γ (right_ne_zero_of_smul hne)⟩

end Formalism.FourierDecayAlt.P.CutSH
