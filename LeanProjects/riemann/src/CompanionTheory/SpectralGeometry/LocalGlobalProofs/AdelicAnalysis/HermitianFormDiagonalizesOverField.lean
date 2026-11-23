import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianNondegRepresentsNonzeroScalar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagHermitian

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgDiag

theorem blockOne_mul {K : Type} [CommRing K] {M : ℕ} (a b : K) (A B : Matrix (Fin M) (Fin M) K) :
    blockOne a A * blockOne b B = blockOne (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockOne_one {K : Type} [CommRing K] {M : ℕ} :
    blockOne (1 : K) (1 : Matrix (Fin M) (Fin M) K) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blockOne, Matrix.one_apply]
  exact fun h => absurd h.symm (Fin.succ_ne_zero _)

def blockGL {K : Type} [CommRing K] {M : ℕ} (h : GL (Fin M) K) : GL (Fin (M + 1)) K where
  val := blockOne 1 (h : Matrix (Fin M) (Fin M) K)
  inv := blockOne 1 ((h⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K)
  val_inv := by rw [blockOne_mul, Units.mul_inv, mul_one, blockOne_one]
  inv_val := by rw [blockOne_mul, Units.inv_mul, mul_one, blockOne_one]

theorem diag_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) :=
  _root_.UpperTheory.Reformulated.B.Gka4.diag_hermitian

end GlobalTheory.CompanionTheory.SW.AlgDiag
