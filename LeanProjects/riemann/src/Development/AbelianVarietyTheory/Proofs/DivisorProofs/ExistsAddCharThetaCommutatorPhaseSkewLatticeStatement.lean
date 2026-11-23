import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addChar_thetaCommutatorPhase_skewLattice : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  first | exact @GlobalTheory.CommPhase.chars | exact GlobalTheory.CommPhase.chars | (intros; apply GlobalTheory.CommPhase.chars <;> assumption)
