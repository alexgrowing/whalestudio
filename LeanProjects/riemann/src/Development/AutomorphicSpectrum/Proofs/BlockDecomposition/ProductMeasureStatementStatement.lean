import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_measure_statement : ProdMeas := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | exact GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas <;> assumption)
