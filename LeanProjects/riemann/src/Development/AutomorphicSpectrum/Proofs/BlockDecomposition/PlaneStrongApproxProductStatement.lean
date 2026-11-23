import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProduct
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_strong_approx_product : Sa2.PropProd := by
  first | exact @GlobalTheory.CompanionTheory.Sa2Prod.propProd | exact GlobalTheory.CompanionTheory.Sa2Prod.propProd | (intros; apply GlobalTheory.CompanionTheory.Sa2Prod.propProd <;> assumption)
