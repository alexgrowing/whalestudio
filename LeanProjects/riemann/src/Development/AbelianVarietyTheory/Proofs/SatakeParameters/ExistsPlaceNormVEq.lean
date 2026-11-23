import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Mathlib
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.PlaceNormDec

theorem exists_place_normV_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range → ∃ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w ∧ IsPlaceOver A w' ∧ normV w' = normV w := by
  intro E Ω _ _ _ _ _ Q w A hA hD
  obtain ⟨w', hw', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω (↥Q.K) w A hA hD
  refine ⟨w', ?_, hw', ?_⟩
  · have hl := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA hw'
    ext x
    show x ∈ (w'.under (𝓞 E)).asIdeal ↔ x ∈ w.asIdeal
    rw [hl.over]
    rfl
  · obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA (↥Q.K) Ω A w' hw' (RingEquiv.refl Ω) (algebraMap E ↥Q.K) i hi
    exact hq

end GlobalTheory.PlaceNormDec
