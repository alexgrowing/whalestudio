import Formalism.HermitianCurvature.LemmaDensOfSteps

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem nonzero_minor_count_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ ≤ r + 2 := by
  unfold Formalism.FourierDecayAlt.DensityAveraging.nzMin
  calc _ ≤ (Finset.univ : Finset (Fin (r + 2))).card := Finset.card_filter_le _ _
    _ = r + 2 := by simp

theorem density_lemma_of_reductions : Formalism.FourierDecayAlt.DensityAveraging.LemmaDensOfSteps := by
  rintro ⟨C0, hB⟩ ⟨C1, hJ⟩ ⟨C2, hT⟩
  refine ⟨max C0 (max C1 C2), ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ O hr hε hA hmm hF hsupp hbig hrel hG
  have H : Formalism.FourierDecayAlt.DensityAveraging.DensHyp (max C0 (max C1 C2)) D A ε mm F' := ⟨hr, hε, hA, hmm, hF, hsupp, hbig⟩
  have h0 : C0 ≤ max C0 (max C1 C2) := le_max_left _ _
  have h1 : C1 ≤ max C0 (max C1 C2) := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : C2 ≤ max C0 (max C1 C2) := le_trans (le_max_right _ _) (le_max_right _ _)
  have key : ∀ n : ℕ, ∀ γ : B.Mat k r, r + 2 - Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ = n → IsRelevant D γ →
      0 < Gf k r D.z D.z' γ → Formalism.FourierDecayAlt.DensityAveraging.VanAt D F' γ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro γ hn hrelγ hGγ
      have hMore : Formalism.FourierDecayAlt.DensityAveraging.MoreBlocks D F' γ := by
        intro γ' hrel' hG' hlt
        have hle := nonzero_minor_count_le D γ'
        exact ih (r + 2 - Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ') (by omega) γ' rfl hrel' hG'
      by_cases hbc : γ ∈ bigPos D
      · exact hB _ h0 k r Wp Wq D A ε mm F' γ H hbc hrelγ
      · have hz : ∃ l : Fin (r + 2), Dmin k r D.z D.z' γ l = 0 := by
          by_contra hne
          exact hbc ⟨hrelγ.1, hGγ, fun l _ hl => hne ⟨l, hl⟩⟩
        by_cases hcj : Formalism.FourierDecayAlt.DensityAveraging.CaseJ D γ
        · exact hJ _ h1 k r Wp Wq D A ε mm F' γ H hrelγ hGγ hcj hMore
        · exact hT _ h2 k r Wp Wq D A ε mm F' γ H hrelγ hGγ ⟨hz, hcj⟩ hMore
  exact key _ γ rfl hrel hG O

end Formalism.FourierDecayAlt.P
