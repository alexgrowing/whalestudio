import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure : ∀ (F σ : Type) [Field F] [Finite σ] (J : Ideal (MvPolynomial σ F)) (f : MvPolynomial σ F), (∀ x : σ → AlgebraicClosure F, (∀ g ∈ J, aeval x g = 0) → aeval x f = 0) → ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (x : σ → Ω), (∀ g ∈ J, aeval x g = 0) → aeval x f = 0 := by
  first | exact @GlobalTheory.vanish_transfer_of_algClosure | exact GlobalTheory.vanish_transfer_of_algClosure | (intros; apply GlobalTheory.vanish_transfer_of_algClosure <;> assumption)
