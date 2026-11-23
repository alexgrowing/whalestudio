import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxIdealSmulMemOfLtOfRelIndexNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximalIdeal_smul_mem_of_lt_of_relIndex_ne_zero : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (N₀ N : Submodule (𝓞 F) V), N₀ < N → N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 → ∃ (u : V) (p : Ideal (𝓞 F)), p.IsMaximal ∧ u ∈ N ∧ u ∉ N₀ ∧ ∀ π ∈ p, π • u ∈ N₀ := by
  first | exact @GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero | exact GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero | (intros; apply GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero <;> assumption)
