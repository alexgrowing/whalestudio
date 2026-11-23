import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLatticeProdDerivWeierstrassPMem
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧ (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  first | exact @GlobalTheory.CMModel.exists_datum_sqProd_mem | exact GlobalTheory.CMModel.exists_datum_sqProd_mem | (intros; apply GlobalTheory.CMModel.exists_datum_sqProd_mem <;> assumption)
