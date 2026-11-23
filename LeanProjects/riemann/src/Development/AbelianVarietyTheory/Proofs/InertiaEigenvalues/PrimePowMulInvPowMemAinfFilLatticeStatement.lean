import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowMulInvPowMemAinfFilLattice
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), Lev l s → ∀ u ∈ FilB P 0, io AI AI.π₁ * u = 1 → ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ a : Ainf l, (l : P.R.BdR) ^ (s * k) * io AI a * u ^ (k + 1) ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | exact GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | (intros; apply GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat <;> assumption)
