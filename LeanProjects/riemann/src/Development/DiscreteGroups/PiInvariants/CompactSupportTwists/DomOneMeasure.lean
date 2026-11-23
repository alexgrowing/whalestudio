import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.UncutHalf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

namespace DiscreteGroups.T1.G

theorem domOne_measure {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    (Γ : Subgroup (X × Y)) (F : Set (X × Y)) (hF : IsFundamentalDomain Γ F (μ₁.prod μ₂))
    (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m) :
    ∃ μ : @Measure (X × Y) m,
      (@Measure.IsMulLeftInvariant _ m _ μ ∧ @Measure.IsMulRightInvariant _ m _ μ ∧
        @Measure.IsOpenPosMeasure _ _ m μ ∧ @IsLocallyFiniteMeasure _ m _ μ) ∧
      @IsFundamentalDomain Γ (X × Y) _ _ m F μ ∧
      (∀ f : X × Y → ℂ, @integral _ _ _ _ m (@Measure.restrict _ m μ F) f =
        @integral _ _ _ _ Prod.instMeasurableSpace ((μ₁.prod μ₂).restrict F) f) ∧
      ∀ f : X × Y → ℂ, Continuous f → HasCompactSupport f →
        @integral _ _ _ _ m μ f = ∫ x₁, ∫ x₂, f (x₁, x₂) ∂μ₂ ∂μ₁ := by
  subst e
  have : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  have : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  refine ⟨μ₁.prod μ₂, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hF, fun _ => rfl,
    fun f hc hs => ?_⟩
  exact integral_prod f (hc.integrable_of_hasCompactSupport hs)

theorem domOne : DomOne := by
  intro E _ _ _ n _ _ _ _ μ₁ _ μ₂ _
  obtain ⟨F₁, h₁⟩ := domEx_holds E n μ₁
  obtain ⟨F₂, h₂⟩ := domEx_holds E 0 μ₂
  have := CuspidalL2GL.locallyCompactSpace_GA E n
  have := CuspidalL2GL.locallyCompactSpace_GA E 0
  have := CuspidalL2GL.secondCountableTopology_GA E n
  have := CuspidalL2GL.secondCountableTopology_GA E 0
  have := GlobalTheory.CompanionTheory.PairDom.isMulRightInvariant_GA E n μ₁
  have := GlobalTheory.CompanionTheory.PairDom.isMulRightInvariant_GA E 0 μ₂
  have : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  have : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨μ, hh, hf, hi, hc⟩ := domOne_measure μ₁ μ₂ (ratH E n 0) (F₁ ×ˢ F₂)
    (GlobalTheory.CompanionTheory.PairDom.isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E n) (ratGL E 0) F₁ F₂ h₁ h₂) (borelH E n 0)
    Prod.borelSpace.measurable_eq
  exact ⟨F₁, F₂, ⟨μ, hh, F₁ ×ˢ F₂, hf⟩, h₁, h₂, fun τ φ => hi _, fun F hF hs => hc F hF hs⟩

end DiscreteGroups.T1.G

end
