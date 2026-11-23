import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TriangularSystemMonomialProductsBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_system_monomial_products_basis : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (t : ℕ → MvPolynomial ℕ R), (∀ i, ∃ (v : Rˣ) (a b : MvPolynomial ℕ R), a ∈ MvPolynomial.supported R (Set.Iio i) ∧ b ∈ MvPolynomial.supported R (Set.Iio i) ∧ t i = MvPolynomial.C (v : R) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) → LinearIndependent R (fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) ∧ Submodule.span R (Set.range fun x : Digits l × (ℕ →₀ ℕ) => MvPolynomial.monomial x.1.1 (1 : R) * x.2.prod fun i n => t i ^ n) = ⊤ := by
  first | exact @GlobalTheory.TriBasis.tri_basis | exact GlobalTheory.TriBasis.tri_basis | (intros; apply GlobalTheory.TriBasis.tri_basis <;> assumption)
