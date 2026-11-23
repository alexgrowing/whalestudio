import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalStabiliserDomains

theorem isDiscreteWithDomains_inf_subgroupOf {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ S : Subgroup G) [Countable Γ] [DiscreteTopology Γ] :
    IsDiscreteWithDomains ((Γ ⊓ S).subgroupOf S) := by
  let f : (Γ ⊓ S).subgroupOf S → Γ := fun g => ⟨g.1.1, g.2.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have : Countable ((Γ ⊓ S).subgroupOf S) := hf.countable
  have : DiscreteTopology ((Γ ⊓ S).subgroupOf S) := DiscreteTopology.of_continuous_injective hc hf
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_HstabFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  intro F E _ _ _ _ _ σ _ M J _ x _
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have h := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ M J
  have := h.1
  have := h.2.1
  exact isDiscreteWithDomains_inf_subgroupOf (ratPts (AF F) σ J) (Hstab (AF F) σ J x)

end GlobalTheory.RationalStabiliserDomains
