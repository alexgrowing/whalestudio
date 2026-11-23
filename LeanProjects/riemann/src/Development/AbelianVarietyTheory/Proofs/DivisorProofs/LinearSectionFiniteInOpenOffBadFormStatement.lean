import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionFiniteInOpenOffBadForm
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSection_finite_inOpen_off_badForm : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → ∀ (g : MvPolynomial (Fin T.N) F), (∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0) → (∀ (K : Type) [Field K] [Algebra F K] (y : Fin T.N → K), {x : T.Pt K | aeval (T.coords x.1) g ≠ 0 ∧ ∃ c : K, T.coords x.1 = c • y}.Finite) → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f ≠ 0 → (∀ x ∈ T.geomPts E (T.linSection E s), aeval (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1) g ≠ 0) → ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite ∧ T.InOpen E (T.linSection E s) := by
  first | exact @GlobalTheory.HSShort.Supp.finite_and_inOpen | exact GlobalTheory.HSShort.Supp.finite_and_inOpen | (intros; apply GlobalTheory.HSShort.Supp.finite_and_inOpen <;> assumption)
