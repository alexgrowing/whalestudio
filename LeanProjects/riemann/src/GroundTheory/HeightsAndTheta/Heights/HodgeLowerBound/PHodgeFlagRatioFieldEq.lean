import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioFieldEq
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagSpan
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPivotMinorFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ObjectsTied
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRatioFieldSpan
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagSpan
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPivotMinorFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenMat0FrEqMap
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioFieldEq.proof (h₁ : RatioFieldSpan.Statement) (h₂ : HodgeFlagSpan.Statement)
    (h₃ : PivotMinorFlag.Statement) (h₄ : GenLeadMinor0NeZero.Statement) : HodgeFlagRatioFieldEq.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc

  have hq : ∀ (τ : Ψ) (i : Fin (D.N - 1)),
      IntermediateField.adjoin Ω (Set.range fun m =>
          Pl.pluecker0 B τ i m / Pl.pluecker0 B τ i (c (Sum.inr (τ, i)))) =
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) := by
    intro τ i
    have hspan := h₂ II Ψ K ι Ω E D Pl H B τ i
    obtain ⟨S₀, hS₀⟩ := h₃ _ D.N (genMat0Fr Ω Ψ D.N D.j τ) i (Fin.castLE (Nat.sub_le D.N 1) i) le_rfl
    refine h₁ Ω Pl.ΩY _ _ _ _ _ _ hspan (Submodule.subset_span ⟨_, rfl⟩) ?_ (hc (Sum.inr (τ, i)))
      (h₄ Ω Ψ D.N D.j τ i)
    rw [hspan]
    exact Submodule.subset_span ⟨S₀, by rw [leadMinor, hS₀]⟩
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | q, t⟩, rfl⟩
    · show Pl.ofΩ (D.y ⟨k, t⟩) / Pl.ofΩ (D.y ⟨k, c (Sum.inl k)⟩) ∈ _
      rw [PlueckerData.ofΩ_eq, PlueckerData.ofΩ_eq, ← map_div₀]
      exact IntermediateField.algebraMap_mem _ _
    · have hmem : Pl.pluecker0 B q.1 q.2 t / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2))) ∈
          IntermediateField.adjoin Ω (Set.range fun m =>
            Pl.pluecker0 B q.1 q.2 m / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2)))) :=
        IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩
      rw [hq] at hmem
      refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
      rintro _ ⟨S, rfl⟩
      exact ⟨(q.1, ⟨q.2, S⟩), rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨τ, i, S⟩, rfl⟩
    have hmem : flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i ∈
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) :=
      IntermediateField.subset_adjoin _ _ ⟨S, rfl⟩
    rw [← hq] at hmem
    refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
    rintro _ ⟨m, rfl⟩
    exact ⟨⟨Sum.inr (τ, i), m⟩, rfl⟩

theorem HodgeFlagRatioFieldEq.full : HodgeFlagRatioFieldEq.Statement :=
  HodgeFlagRatioFieldEq.proof RatioFieldSpan.full HodgeFlagSpan.full PivotMinorFlag.full GenLeadMinor0NeZero.full

end GroundTheory.Heights₂.Heights.LowerBoundFree
