import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteTopology_rationalPoints_hermitianSpace : ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) := by
  first | exact @GlobalTheory.RationalDiscrete.discreteTopology_GQ | exact GlobalTheory.RationalDiscrete.discreteTopology_GQ | (intros; apply GlobalTheory.RationalDiscrete.discreteTopology_GQ <;> assumption)
