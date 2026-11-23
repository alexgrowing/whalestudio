import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LiftOneFormsToCompatibleApply
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapNon

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions
open Formalism.L2.Th1.H (IsSelfDual)

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem kappaAt_of (hsd : IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) B.latA) (hcc : cc ≠ ⊥) (h0 : δ ≠ 0)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : B.KappaAt p ι := by
  by_cases hs : SplitK D p
  · exact kappaAt_split B hsd p ι hs
  · exact kappaAt_nonsplit_of B h0 hcc p hs ι (kappa_norm_nonsplit B.kc ι hs)

theorem kappaAt (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) :
    B.KappaAt p ι :=
  kappaAt_of B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual B hcc hδ) hcc.1 (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B) p ι

theorem kappaAll (D : D7) : KappaAll D :=
  fun _ _ B hcc hδ p _ ι _ => kappaAt B hcc hδ p ι

theorem kappaSplit (D : D7) : KappaSplit D :=
  fun _ _ B hcc hδ p _ ι _ => kappaAt B hcc hδ p ι

end Formalism.L2.Ker.KS
