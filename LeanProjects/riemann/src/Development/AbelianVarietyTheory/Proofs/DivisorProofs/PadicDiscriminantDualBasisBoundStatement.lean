import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicDiscriminantDualBasisBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdemEvalAndDualDiffIff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuesOfDiscrFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBIdemDen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_discriminant_dual_basis_bound : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (φ : E →+* ℂ_[p]), ∃ (d : ℂ_[p]) (n : ℕ) (r : Fin n → 𝓞_ℂ_[p]) (a : Fin n → 𝓞 E), (p : ℝ) ^ (-((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))) ≤ ‖d‖ ∧ ∀ σ : E →+* ℂ_[p], ∑ k, algebraMap 𝓞_ℂ_[p] ℂ_[p] (r k) * σ (a k) = if σ = φ then d else 0 := by
  first | exact @GlobalTheory.IdemDenominatorCp.idem_denominator | exact GlobalTheory.IdemDenominatorCp.idem_denominator | (intros; apply GlobalTheory.IdemDenominatorCp.idem_denominator <;> assumption)
