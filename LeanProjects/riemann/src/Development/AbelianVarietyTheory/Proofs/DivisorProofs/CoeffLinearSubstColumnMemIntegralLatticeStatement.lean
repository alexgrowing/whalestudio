import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_linearSubst_column_mem_integralLattice : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, coeff m (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) • b i ∈ S.M S.T := by
  first | exact @GlobalTheory.HSShort.colCoeff_mem | exact GlobalTheory.HSShort.colCoeff_mem | (intros; apply GlobalTheory.HSShort.colCoeff_mem <;> assumption)
