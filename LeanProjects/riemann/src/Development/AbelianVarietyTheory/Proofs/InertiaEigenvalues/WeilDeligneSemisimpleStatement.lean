import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_semisimple : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | exact GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho | (intros; apply GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho <;> assumption)
