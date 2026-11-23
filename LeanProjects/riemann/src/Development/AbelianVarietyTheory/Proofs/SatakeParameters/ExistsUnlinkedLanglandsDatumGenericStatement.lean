import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnlinkedLanglandsDatumGeneric
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
theorem _root_.GlobalTheory.T.exists_unlinked_langlandsDatum_generic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL k), IsGeneric x.rep →
    ∃ (c : ℕ) (Δ : Fin c → Segment k), (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧
      IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep := by
  first | (exact @GlobalTheory.GenericLDatum.exists_unlinked_isL) | (exact GlobalTheory.GenericLDatum.exists_unlinked_isL) | (intros; apply GlobalTheory.GenericLDatum.exists_unlinked_isL  <;> assumption)
