import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsMixMaximalMinorFockVectorsUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_mix_maximalMinorFockVectors_unitary : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ k ∈ GinfC X.B, ∃ U : Matrix (Tup D P.a P.d P.n) (Tup D P.a P.d P.n) ℂ, U ∈ Matrix.unitaryGroup (Tup D P.a P.d P.n) ℂ ∧
    ∀ T, X.om (1, k) (X.fock T) = ∑ T', U T T' • X.fock T' := by
  first | exact @GlobalTheory.NormDict.RealB.real_mix | exact GlobalTheory.NormDict.RealB.real_mix | (intros; apply GlobalTheory.NormDict.RealB.real_mix <;> assumption)
