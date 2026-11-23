import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R] (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) → Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧ (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) → ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by
  first | exact @GlobalTheory.eigenMult_of_dense | exact GlobalTheory.eigenMult_of_dense | (intros; apply GlobalTheory.eigenMult_of_dense <;> assumption)
