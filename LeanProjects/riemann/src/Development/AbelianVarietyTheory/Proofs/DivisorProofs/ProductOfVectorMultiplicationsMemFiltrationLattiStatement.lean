import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLatti
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  first | exact @GlobalTheory.HSShort.wordMem | exact GlobalTheory.HSShort.wordMem | (intros; apply GlobalTheory.HSShort.wordMem <;> assumption)
