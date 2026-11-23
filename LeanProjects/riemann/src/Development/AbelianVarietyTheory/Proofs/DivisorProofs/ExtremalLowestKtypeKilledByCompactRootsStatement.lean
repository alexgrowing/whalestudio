import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremal_lowest_Ktype_killed_by_compact_roots : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), IsDS ε lam σ → ∀ v ∈ lowKSub ε lam σ, SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v → IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → (∀ a, dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a a 1) v = ((Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a) : ℝ) : ℂ) • v) ∧ ∀ a c : Fin n, ε a = ε c → revNeg ε a < revNeg ε c → dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  first | exact @GlobalTheory.HolDict.BorelK.extremal_killed | exact GlobalTheory.HolDict.BorelK.extremal_killed | (intros; apply GlobalTheory.HolDict.BorelK.extremal_killed <;> assumption)
