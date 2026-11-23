import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphericalComm

theorem exists_unif_of_not_dvd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (h : ¬ P.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 E)) :
    ∃ x : 𝓞 F, ∃ y : 𝓞 E, (y : E) = algebraMap F E (x : F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  by_contra hne
  push Not at hne
  apply h
  have hle : (P.asIdeal.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hne x _ rfl hx
  haveI := P.isMaximal
  haveI : (P.asIdeal.under (𝓞 F)).IsMaximal := Ideal.IsMaximal.under _ _
  have hb : P.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot _ P.ne_bot
  have := pow_sub_one_dvd_differentIdeal (𝓞 F) P.asIdeal 2 hb (Ideal.dvd_iff_le.2 hle)
  simpa using this

end GlobalTheory.SphericalComm
