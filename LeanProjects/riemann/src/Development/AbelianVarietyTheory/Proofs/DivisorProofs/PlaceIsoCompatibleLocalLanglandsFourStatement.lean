import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsFour
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
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_four : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → (∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ (x : IrrGL (w'.adicCompletion E')) ω, HasCentralChar x.rep ω → ∀ σ, ‖((rc' x).eig σ).prod‖ = ‖(ω (a' σ) : ℂ)‖) ∧ (∀ x χ hχ, UpperTheory.Zero.LLC.Good x → rc' (x.tw χ hχ) = (rc' x).lpChar (rc' (.ofChar χ hχ))) ∧ (∀ (x : IrrGL (w'.adicCompletion E')) ω, UpperTheory.Zero.LLC.Good x → HasCentralChar x.rep ω → ∀ σ, ((rc' x).eig σ).prod = (ω (a' σ) : ℂ)) ∧ (∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w'.adicCompletion E'))), UpperTheory.Zero.LLC.Good (cls π) → Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc' (cls π') = (rc' (cls π)).lpDual) ∧ (∀ x y, UpperTheory.Zero.LLC.Good y → rc' x = rc' y → x = y) := by
  first | (exact @GlobalTheory.LawsTTransport.lawsT_transport) | (exact GlobalTheory.LawsTTransport.lawsT_transport) | (intros; apply GlobalTheory.LawsTTransport.lawsT_transport  <;> assumption)
