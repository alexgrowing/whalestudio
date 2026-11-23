import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitHermitianGeneratorsExist
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
open NumberField GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_hermitian_generators_exist : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (D : ConjData C p (𝓞 E) d) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ i, ∃ x : Fin r → (Fin d → K) × (Fin d → K), LinearIndependent K (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => D.ρH (RingOfIntegers.basis E q.2) (x q.1)) ∧ ∀ y, y ∈ D.H i ↔ ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • D.ρH (RingOfIntegers.basis E q.2) (x q.1)) → deg C (quot C D.H (⨆ a : 𝓞 E, LinearMap.range (D.ρH a - χ a • LinearMap.id))) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.deg_quot_eq_zero <;> assumption)
