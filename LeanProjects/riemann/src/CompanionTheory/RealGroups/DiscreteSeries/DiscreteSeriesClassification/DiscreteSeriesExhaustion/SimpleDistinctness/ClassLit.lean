import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.KTypesAbove
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatioStatement

namespace CompanionTheory.RgExh.Fin

theorem dsClass_of (hX : GlobalTheory.Dec.DSExhaust) : GlobalTheory.DSId.DSClass := by
  intro n
  have key : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), Formalism.QuantumDeterminants.IsHCParam lam → GlobalTheory.DSId.IsHCDS ε lam π ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
          Formalism.MainNotions.S.IsDS ε lam σ → GlobalTheory.Dec.UEquiv ε σ π := by
    intro ε lam
    by_cases hl : Formalism.QuantumDeterminants.IsHCParam lam
    · obtain ⟨G, i1, i2, π, h1, h2⟩ := CompanionTheory.RgDs.B.classUsed n ε lam hl
      exact ⟨G, i1, i2, π, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨ℂ, inferInstance, inferInstance, fun _ => 0, fun h => absurd h hl⟩
  choose G i1 i2 π hπ using key
  refine ⟨G, i1, i2, π, fun ε lam hl => (hπ ε lam hl).1, fun ε H' _ _ σ' hσ' => ?_⟩
  obtain ⟨s, mu, hm, hs, hds⟩ := hX n ε H' σ' hσ'
  exact ⟨s, mu, hm, hs, (hπ (ε ∘ s) mu hm).2 H' _ hds⟩

theorem discreteSeriesClassification_of (hX : GlobalTheory.Dec.DSExhaust) : GlobalTheory.Published.DiscreteSeriesClassification :=
  GlobalTheory.Published.discreteSeriesClassification_iff.2 (dsClass_of hX)

theorem discreteSeriesCover_of (hX : GlobalTheory.Dec.DSExhaust) : GlobalTheory.Published.DiscreteSeriesCover :=
  GlobalTheory.T.discreteSeries_detSqrtCover_of_unitary_classification (discreteSeriesClassification_of hX)

end CompanionTheory.RgExh.Fin
