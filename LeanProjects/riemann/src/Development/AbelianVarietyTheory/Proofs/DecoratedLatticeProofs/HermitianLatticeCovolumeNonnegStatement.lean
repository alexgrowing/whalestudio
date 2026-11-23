import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLatticeCovolumeNonneg
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_covolume_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), IsRatHerm K0 G X → ∀ N : Submodule (𝓞 K) (Fin n → K), N.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (R := 𝓞 K) (hform G) N → 0 ≤ lcv X N := by
  first | exact @GlobalTheory.lcv_nonneg_of_integral_submodule | exact GlobalTheory.lcv_nonneg_of_integral_submodule | (intros; apply GlobalTheory.lcv_nonneg_of_integral_submodule <;> assumption)
