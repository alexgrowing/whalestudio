import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.LinearIndepOnOfInvariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace UpperTheory.Lit.Drps

open DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem eD_alg (T : LocTied6 l P AI) (q : ℚ_[l]) : T.eD (algebraMap ℚ_[l] P.R.BdR q) = qQ l q := by
  rw [PositivityTheory.LocInh.tie_qD T, ← PositivityTheory.LocInh.ιCD_qB, ← period_ring_base.BaseA.ι_eq, ← period_ring_base.BaseA.qB_eq, period_ring_base.base_ι_q]

end UpperTheory.Lit.Drps
