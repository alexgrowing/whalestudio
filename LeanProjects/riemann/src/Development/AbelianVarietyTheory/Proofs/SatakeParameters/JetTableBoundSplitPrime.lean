import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms

namespace GlobalTheory.AtG

theorem jetSplitAmb_holds : JetSplitAmb := by
  intro D X s cc δ B χ cD hok hcc hδ hχ a b S N N' p _ ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m
  exact Formalism.L2.Ker.Test.jetAtSplit_ambOf s B χ cD hok hcc hδ hχ a b S N N' p ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m

end GlobalTheory.AtG
