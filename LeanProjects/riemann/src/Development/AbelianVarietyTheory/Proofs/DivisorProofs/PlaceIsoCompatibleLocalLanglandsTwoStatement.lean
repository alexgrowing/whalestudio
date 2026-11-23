import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsTwo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_two : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → UpperTheory.Zero.LLC.TypeLaw h rc → UpperTheory.Zero.LLC.TypeLaw h' rc' := by
  first | (exact @GlobalTheory.TypeLawTransport.typeLaw_transport_fwd) | (exact GlobalTheory.TypeLawTransport.typeLaw_transport_fwd) | (intros; apply GlobalTheory.TypeLawTransport.typeLaw_transport_fwd  <;> assumption)
