import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneJacobianIdentity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem smOf : SmOf := by
  intro F E _ _ _ _ _ σ h n J _ f hf k γ hγ g
  exact (GlobalTheory.Orb.isSmoothRealFam_prod (fun i =>
    (GlobalTheory.ThK.CuspTransfer.Smooth.line_fam h (hγ i)).1.comp (contDiff_apply ℝ ℝ i))).contDiff hf g

end MainStatements.WeightKernel.Dec

end
