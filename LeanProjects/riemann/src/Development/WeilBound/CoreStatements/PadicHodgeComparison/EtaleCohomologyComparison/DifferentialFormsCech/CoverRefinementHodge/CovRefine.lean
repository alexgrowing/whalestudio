import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om.Nt2

def CovRefine : Prop :=
  ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsSeparated q] [QuasiCompact q]
    {κ : Type} (V : κ → X.Opens), iSup V = ⊤ → ∃ U : Pb.Cov q, ∀ α, ∃ k, U.U α ≤ V k

def PullHId : Prop :=
  ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (h : 𝟙 X ≫ q = q) (a n : ℕ)
    (x : HT.Hdg q a n), HT.pullH (𝟙 X) h a n x = x

def PullCId : Prop :=
  ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (h : 𝟙 X ≫ q = q) (a j : ℕ)
    (x : HodgeC q a j), pullC (𝟙 X) h a j x = x

end CrystallineSemistableComparison.Om.Nt2
