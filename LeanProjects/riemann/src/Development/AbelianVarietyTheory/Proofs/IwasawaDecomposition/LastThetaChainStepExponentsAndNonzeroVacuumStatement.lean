import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaChainStepExponentsAndNonzeroVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastThetaChainStep_exponents_and_nonzero_vacuum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωX → R.chain_vX → ∀ t (k : Fin D.R.m), (k : ℕ) = D.R.m - 1 → IsStepWeil k R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ωX t) ∧ IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := by
  first | exact @GlobalTheory.LastStepVac.last_step | exact GlobalTheory.LastStepVac.last_step | (intros; apply GlobalTheory.LastStepVac.last_step <;> assumption)
