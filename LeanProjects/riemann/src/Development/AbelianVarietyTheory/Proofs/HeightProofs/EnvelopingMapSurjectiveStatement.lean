import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_map_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau), Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  first | exact @GlobalTheory.EnvWords.envOf_surjective | exact GlobalTheory.EnvWords.envOf_surjective | (intros; apply GlobalTheory.EnvWords.envOf_surjective <;> assumption)
