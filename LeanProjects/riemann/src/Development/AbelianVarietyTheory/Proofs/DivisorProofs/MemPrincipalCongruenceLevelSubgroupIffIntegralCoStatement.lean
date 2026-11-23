import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_principalCongruenceLevelSubgroup_iff_integral_congruent : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (k : GA D N), k ∈ congLev D 𝔪 N ↔ k ∈ intG D N ∧ CongOne D 𝔪 k := by
  first | exact @GlobalTheory.FunObj.StdDatum.mem_congLev_iff | exact GlobalTheory.FunObj.StdDatum.mem_congLev_iff | (intros; apply GlobalTheory.FunObj.StdDatum.mem_congLev_iff <;> assumption)
