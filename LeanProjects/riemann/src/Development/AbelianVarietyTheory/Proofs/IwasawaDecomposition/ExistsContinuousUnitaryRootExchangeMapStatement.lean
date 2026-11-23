import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitaryRootExchangeMap : ∀ (D : D7) (B : HSp D) (η : AE D), η * cA D η = 0 → ∀ v : Fin B.rank → AE D, ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B, Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  first | exact @GlobalTheory.RootUnip.exists_continuous_isK | exact GlobalTheory.RootUnip.exists_continuous_isK | (intros; apply GlobalTheory.RootUnip.exists_continuous_isK <;> assumption)
