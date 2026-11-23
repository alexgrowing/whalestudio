import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalUnitaryDomains

theorem isDiscreteWithDomains_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [hc : Countable Γ] [hd : DiscreteTopology Γ] : IsDiscreteWithDomains Γ := by
  refine ⟨hc, hd, fun μ _ => ?_⟩
  obtain ⟨𝓕, hF, h⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  exact ⟨𝓕, hF, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem isDiscreteWithDomains_ratPts' (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have : Countable (ratPts (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : DiscreteTopology (ratPts (AF F) σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  exact isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) :=
  fun F E _ _ _ _ _ σ _ M J _ => isDiscreteWithDomains_ratPts' F E σ M J

end GlobalTheory.RationalUnitaryDomains
