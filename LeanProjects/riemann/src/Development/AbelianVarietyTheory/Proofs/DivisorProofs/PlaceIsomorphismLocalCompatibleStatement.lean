import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsomorphismLocalCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_isomorphism_local_compatible : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → (∃ rc₀ : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc₀) → ∃ rc' : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc' ∧ ∀ x x', GlobalTheory.LocLanglands.RepRel i x x' → GlobalTheory.LocLanglands.WDRel (RingEquiv.refl Ω) (rc x) (rc' x') := by
  first | (exact @GlobalTheory.RecTTransport.isRecT_transport) | (exact GlobalTheory.RecTTransport.isRecT_transport) | (intros; apply GlobalTheory.RecTTransport.isRecT_transport <;> assumption)
