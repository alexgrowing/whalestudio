import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerRatioFieldEq
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerSpan
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPivotMinorFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGenLeadMinorNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem PlueckerRatioFieldEq.proof (h₁ : RatioFieldSpan.Statement) (h₂ : PlueckerSpan.Statement)
    (h₃ : PivotMinorFlag.Statement) (h₄ : GenLeadMinorNeZero.Statement) : PlueckerRatioFieldEq.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl c hc

  have hq : ∀ (τ : Ψ) (i : Fin (D.N - 1)),
      IntermediateField.adjoin Ω (Set.range fun m => Pl.pluecker τ i m / Pl.pluecker τ i (c (Sum.inr (τ, i)))) =
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMatFr Ω Ψ D.N τ) i S / leadMinor (genMatFr Ω Ψ D.N τ) i) := by
    intro τ i
    have hspan := h₂ II Ψ K ι Ω E D Pl τ i
    obtain ⟨S₀, hS₀⟩ := h₃ _ D.N (genMatFr Ω Ψ D.N τ) i (Fin.castLE (Nat.sub_le D.N 1) i) le_rfl
    refine h₁ Ω Pl.ΩY _ _ _ _ _ _ hspan (Submodule.subset_span ⟨_, rfl⟩) ?_ (hc (Sum.inr (τ, i))) (h₄ Ω Ψ D.N τ i)
    rw [hspan]
    exact Submodule.subset_span ⟨S₀, by rw [leadMinor, hS₀]⟩
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | q, t⟩, rfl⟩
    · show Pl.ofΩ (D.y ⟨k, t⟩) / Pl.ofΩ (D.y ⟨k, c (Sum.inl k)⟩) ∈ _
      rw [PlueckerData.ofΩ_eq, PlueckerData.ofΩ_eq, ← map_div₀]
      exact IntermediateField.algebraMap_mem _ _
    · have hmem : Pl.pluecker q.1 q.2 t / Pl.pluecker q.1 q.2 (c (Sum.inr (q.1, q.2))) ∈
          IntermediateField.adjoin Ω (Set.range fun m =>
            Pl.pluecker q.1 q.2 m / Pl.pluecker q.1 q.2 (c (Sum.inr (q.1, q.2)))) :=
        IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩
      rw [hq] at hmem
      refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
      rintro _ ⟨S, rfl⟩
      exact ⟨(q.1, ⟨q.2, S⟩), rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨τ, i, S⟩, rfl⟩
    have hmem : flagMinor (genMatFr Ω Ψ D.N τ) i S / leadMinor (genMatFr Ω Ψ D.N τ) i ∈
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMatFr Ω Ψ D.N τ) i S / leadMinor (genMatFr Ω Ψ D.N τ) i) :=
      IntermediateField.subset_adjoin _ _ ⟨S, rfl⟩
    rw [← hq] at hmem
    refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
    rintro _ ⟨m, rfl⟩
    exact ⟨⟨Sum.inr (τ, i), m⟩, rfl⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
