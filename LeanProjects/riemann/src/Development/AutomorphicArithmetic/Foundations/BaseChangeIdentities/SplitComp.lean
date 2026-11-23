import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities

theorem splitComp (H : GlobalTheory.BcSpeh.BcSpeh) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    (n : ℕ) (hn : 1 ≤ n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) :
    ∃ P : ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → SmIrr (GL (Fin n) (w.adicCompletion E)),
      ∀ w (hw : IsSplitAt w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (P w hw).ρ := by
  obtain ⟨c, a, d, h, -, -, -, σ, -, -, hs⟩ := H E hE n hn π hπ
  exact ⟨fun w hw =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := (hs w hw).1 }, hs⟩

end UpperTheory.BaseChangeIdentities

end
