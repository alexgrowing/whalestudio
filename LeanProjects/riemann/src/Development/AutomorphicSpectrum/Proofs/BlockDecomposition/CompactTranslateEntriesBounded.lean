import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.KHBound

theorem modulus_det_integralGL {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    modulus (k.val).det = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have hdet : ∀ A : Matrix (Fin 2) (Fin 2) F, (∀ i j, A i j ∈ 𝒪[F]) → A.det ∈ 𝒪[F] := fun A hA => by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (hA 0 0) (hA 1 1)) (mul_mem (hA 0 1) (hA 1 0))
  have a1 := modulus_le_one_iff.2 (hdet _ h1)
  have a2 := modulus_le_one_iff.2 (hdet _ h2)
  have e : (k.val).det * ((k⁻¹ : GL (Fin 2) F).val).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have e' : modulus (k.val).det * modulus ((k⁻¹ : GL (Fin 2) F).val).det = 1 := by
    rw [← modulus_mul, e, modulus_one]
  refine le_antisymm a1 ?_
  calc (1 : NNReal) = modulus (k.val).det * modulus ((k⁻¹ : GL (Fin 2) F).val).det := e'.symm
    _ ≤ modulus (k.val).det * 1 := mul_le_mul_of_nonneg_left a2 zero_le
    _ = modulus (k.val).det := mul_one _

theorem entries_det_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (h₀ : GL (Fin 2) F), ∃ M : ℝ, 0 < M ∧ ∀ k ∈ GLnLocal.integralGL F 2, (∀ i j, (modulus ((k * h₀).val i j) : ℝ) ≤ M) ∧ modulus ((k * h₀).val).det = modulus (h₀.val).det := by
  intro F _ _ _ _ _ _ h₀
  refine ⟨1 + ∑ i, ∑ j, (modulus ((h₀.val) i j) : ℝ), ?_, ?_⟩
  · have : 0 ≤ ∑ i, ∑ j, (modulus ((h₀.val) i j) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    linarith
  intro k hk
  constructor
  · intro i j
    have hb : ∀ a b, (modulus ((h₀.val) a b) : ℝ) ≤ 1 + ∑ i, ∑ j, (modulus ((h₀.val) i j) : ℝ) := by
      intro a b
      have s1 : (modulus ((h₀.val) a b) : ℝ) ≤ ∑ j, (modulus ((h₀.val) a j) : ℝ) :=
        Finset.single_le_sum (f := fun j => (modulus ((h₀.val) a j) : ℝ))
          (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ b)
      have s2 : ∑ j, (modulus ((h₀.val) a j) : ℝ) ≤ ∑ i, ∑ j, (modulus ((h₀.val) i j) : ℝ) :=
        Finset.single_le_sum (f := fun i => ∑ j, (modulus ((h₀.val) i j) : ℝ))
          (fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ a)
      linarith
    have := GlobalTheory.CompanionTheory.LFCoords.modulus_mul_entry_le
      (κ := k.val) (k := h₀.val) ((GLnLocal.mem_integralGL_iff F 2).1 hk).1 hb i j
    simpa [Units.val_mul] using this
  · rw [Units.val_mul, Matrix.det_mul, modulus_mul, modulus_det_integralGL hk, one_mul]

end GlobalTheory.CompanionTheory.KHBound
