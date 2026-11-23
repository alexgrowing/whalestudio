import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocalCmp2
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem foundData_nonempty (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) :
    Nonempty (FoundData Kf S l r ζ Av μ M ρ) := by
  obtain ⟨e, he⟩ := gsEquiv_toGS' Kf.1 (S : Set (HeightOneSpectrum (𝓞 Kf.1)))
  obtain ⟨ιs, ev, hc, hι, hev⟩ := localCmp2' Kf.1 S Av hAv e he
  obtain ⟨A, hA, eM, hM⟩ := repCmp e ρ hρ
  obtain ⟨eD, hD, hDζ⟩ := dualCmp' Kf S hr ζ hζ hS e he μ hμ ρ A eM hM
  exact ⟨⟨e, he, ιs, ev, hc, hev, hι, A, hA, eM, hM, eD, hD, hDζ⟩⟩

end PositivityTheory.Lit1.PTN
