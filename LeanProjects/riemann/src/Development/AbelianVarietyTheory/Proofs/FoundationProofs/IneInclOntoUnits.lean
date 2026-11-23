import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.TypesChars
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PsType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PsType

theorem ineIncl_onto_units : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ u : (w.adicCompletion E)ˣ, valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 → ∃ s : ↥(Ine (F := E) A), a (ineIncl h s) = u) ∧ ∀ s : ↥(Ine (F := E) A), valuation (w.adicCompletion E) (a (ineIncl h s) : w.adicCompletion E) = 1 := by
  intro E Ω _ _ _ _ _ A w h a ha
  refine ⟨fun u hu => ?_, fun s => ?_⟩
  · obtain ⟨τ, rfl⟩ := ha.surj u
    have hdeg : deg τ = 0 := by
      have := ha.ord_eq τ
      rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 hu] at this
      omega
    exact ⟨⟨τ, deg_eq_zero_iff.1 hdeg⟩, congrArg a (Subtype.ext (by rw [coe_ineIncl]))⟩
  · exact GlobalTheory.SmGL.ord_eq_zero_iff.1 (by rw [ha.ord_eq, deg_ineIncl, neg_zero])

end GlobalTheory.PsType
