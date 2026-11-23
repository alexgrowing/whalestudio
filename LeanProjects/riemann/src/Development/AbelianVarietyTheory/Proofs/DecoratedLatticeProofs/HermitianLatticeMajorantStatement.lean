import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLatticeMajorant
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muMaxDual_nonpos_of_dual_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (A : HLat K) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (e : (Fin n → K) ≃ₗ[K] A.V) (M : Submodule (𝓞 K) (Fin n → K)), A.Good → 0 < A.rank → (∀ i j, H i j ∈ K0) → (∀ (v : InfinitePlace K) (i j : Fin n), Formalism.HermitianLatticesTheory.majAt A.b A.X v (e (Pi.single i 1)) (e (Pi.single j 1)) = v.embedding (H i j)) → A.L = M.map (e.toLinearMap.restrictScalars (𝓞 K)) → Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → A.muMaxDual ≤ 0 := by
  first | exact @GlobalTheory.SelfDualSlope.muMaxDual_nonpos_of_rat_coord | exact GlobalTheory.SelfDualSlope.muMaxDual_nonpos_of_rat_coord | (intros; apply GlobalTheory.SelfDualSlope.muMaxDual_nonpos_of_rat_coord <;> assumption)
