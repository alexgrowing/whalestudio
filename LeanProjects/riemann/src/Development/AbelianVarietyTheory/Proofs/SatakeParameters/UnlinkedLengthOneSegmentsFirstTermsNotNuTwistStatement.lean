import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedLengthOneSegmentsFirstTermsNotNuTwist
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unlinkedLengthOneSegments_firstTerms_not_nuTwist : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (c : ℕ) (Δ : Fin c → Segment (w.adicCompletion E)), (∀ i, (Δ i).len = 1) →
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) →
      GlobalTheory.RoadU.Unlinked (Finset.univ.val.map fun i => (Δ i).first) := by
  first | (exact @GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one) | (exact GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one) | (intros; apply GlobalTheory.UnlinkedFirst.unlinked_first_of_len_one  <;> assumption)
