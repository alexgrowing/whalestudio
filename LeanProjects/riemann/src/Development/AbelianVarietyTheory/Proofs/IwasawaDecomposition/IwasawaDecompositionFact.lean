import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationEqOfMemIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem Dec_valuation_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first
  | exact @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | (apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq ..)

end GlobalTheory
