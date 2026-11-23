import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDerivWeierstrassPHalfPeriodsDiscriminant
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant : ∀ (L : PeriodPair) (a b t : ℂ), a ∉ L.lattice → b ∉ L.lattice → a + b ∉ L.lattice → 2 * a ∈ L.lattice → 2 * b ∈ L.lattice → 2 * t ∉ L.lattice → L.derivWeierstrassP t * L.derivWeierstrassP (t + a) * L.derivWeierstrassP (t + b) * L.derivWeierstrassP (t + (a + b)) = (latticeCurve L).Δ := by
  first | exact @GlobalTheory.CMModel.prod_derivWeierstrassP_translates_eq_Δ | exact GlobalTheory.CMModel.prod_derivWeierstrassP_translates_eq_Δ | (intros; apply GlobalTheory.CMModel.prod_derivWeierstrassP_translates_eq_Δ <;> assumption)
