import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystem
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∀ (W : S.Y.Opens) (a : Γ(S.Y, W)), ∃ (d : ℕ) (P Q : MvPolynomial (Fin S.N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ Q ∉ S.imageIdeal ∧ (a ≠ 0 → P ∉ S.imageIdeal) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), ptOf x.1 ∈ W → valR x.1 W a * aeval (S.coords x.1) Q = aeval (S.coords x.1) P := by
  first | exact @GlobalTheory.HSShort.FormRatio.exists_forms | exact GlobalTheory.HSShort.FormRatio.exists_forms | (intros; apply GlobalTheory.HSShort.FormRatio.exists_forms <;> assumption)
