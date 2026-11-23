import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexSupSpanSingletonEqAbsNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_sup_span_singleton_eq_absNorm_of_isMaximal : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (N₀ : Submodule (𝓞 F) V) (u : V) (p : Ideal (𝓞 F)), p.IsMaximal → u ∉ N₀ → (∀ π ∈ p, π • u ∈ N₀) → N₀.toAddSubgroup.relIndex (N₀ ⊔ Submodule.span (𝓞 F) {u}).toAddSubgroup = Ideal.absNorm p := by
  first | exact @GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | exact GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | (intros; apply GlobalTheory.relIndex_sup_span_singleton_eq_absNorm <;> assumption)
