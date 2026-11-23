import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.IntegralKernel

theorem exists_clear_denominators {g : ℕ} (w : Fin g → ℚ) :
    ∃ (D : ℤ) (v : Fin g → ℤ), D ≠ 0 ∧ ∀ i, (v i : ℚ) = (D : ℚ) * w i := by
  classical
  have hdvd : ∀ i, ∃ k : ℤ, (∏ j, ((w j).den : ℤ)) = ((w i).den : ℤ) * k := fun i =>
    Finset.dvd_prod_of_mem (fun j => ((w j).den : ℤ)) (Finset.mem_univ i)
  choose k hk using hdvd
  refine ⟨∏ j, ((w j).den : ℤ), fun i => (w i).num * k i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (w j).den_nz
  · intro i
    rw [hk i]
    push_cast
    have h := Rat.mul_den_eq_num (w i)
    rw [← h]
    ring

theorem cast_mulVec {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) (i : Fin g) :
    (((S *ᵥ v) i : ℤ) : ℚ) = ((S.map (Int.cast : ℤ → ℚ)) *ᵥ (fun j => (v j : ℚ))) i := by
  simp [Matrix.mulVec, dotProduct]

theorem exists_smul_eq_mulVec (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) (hS : Sᵀ = S)
    (u : Fin g → ℤ) (hu : ∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) :
    ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  classical
  let Sq : Matrix (Fin g) (Fin g) ℚ := S.map (Int.cast : ℤ → ℚ)
  let uq : Fin g → ℚ := fun i => (u i : ℚ)
  have hSq : Sqᵀ = Sq := by
    ext i j
    have := congrFun (congrFun hS i) j
    simp only [Matrix.transpose_apply] at this
    simp [Sq, this]

  have hker : ∀ w : Fin g → ℚ, Sq *ᵥ w = 0 → uq ⬝ᵥ w = 0 := by
    intro w hw
    obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators w
    have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • w := by
      funext j; simp [hv j]
    have hSv : S *ᵥ v = 0 := by
      funext i
      have h1 := cast_mulVec S v i
      rw [hvq, Matrix.mulVec_smul] at h1
      have h2 : (((S *ᵥ v) i : ℤ) : ℚ) = 0 := by
        rw [h1]
        change ((D : ℚ) • (Sq *ᵥ w)) i = 0
        rw [hw]; simp
      exact_mod_cast h2
    have h0 := hu v hSv
    have h1 : ((u ⬝ᵥ v : ℤ) : ℚ) = (D : ℚ) * (uq ⬝ᵥ w) := by
      simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, hv, uq]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0] at h1
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    simpa [hDq] using h1.symm
  let f : (Fin g → ℚ) →ₗ[ℚ] (Fin g → ℚ) := Sq.mulVecLin
  let φ : Module.Dual ℚ (Fin g → ℚ) :=
    { toFun := fun w => uq ⬝ᵥ w
      map_add' := fun a b => dotProduct_add uq a b
      map_smul' := fun r a => by simp [dotProduct_smul] }
  have hφ : φ ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact hker w (by simpa [f] using hw)
  obtain ⟨ψ, hψ⟩ := hφ
  let c : Fin g → ℚ := fun i => ψ (Pi.single i 1)
  have hψc : ∀ w, ψ w = c ⬝ᵥ w := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ' w]
    simp [map_sum, c, dotProduct, mul_comm]
  have hu_eq : uq = Sq *ᵥ c := by
    funext i
    have h1 : φ (Pi.single i 1) = uq i := by
      change uq ⬝ᵥ Pi.single i 1 = uq i
      simp
    have h2 : φ (Pi.single i 1) = ψ (Sq *ᵥ Pi.single i 1) := by
      rw [← hψ]; rfl
    rw [← h1, h2, hψc, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSq]
    simp
  obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators c
  refine ⟨D, v, hD, ?_⟩
  funext i
  have h1 := cast_mulVec S v i
  have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • c := by
    funext j; simp [hv j]
  rw [hvq, Matrix.mulVec_smul] at h1
  have h2 : (((D • u) i : ℤ) : ℚ) = (((S *ᵥ v) i : ℤ) : ℚ) := by
    rw [h1]
    change _ = ((D : ℚ) • (Sq *ᵥ c)) i
    rw [← hu_eq]
    simp [uq]
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.IntegralKernel
