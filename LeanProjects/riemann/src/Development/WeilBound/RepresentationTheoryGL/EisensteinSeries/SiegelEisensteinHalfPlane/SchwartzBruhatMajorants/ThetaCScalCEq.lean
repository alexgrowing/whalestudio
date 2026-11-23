import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.MeasurePreservingCompEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPiStatement

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinRankN.Hd

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_scalC (a : IdeleGroup k) :
    Matrix.GeneralLinearGroup.det (scalC a : GL ι 𝔸[k]) = a ^ Fintype.card ι := by
  ext
  simp [scalC, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]

theorem tInv_scalC (a : IdeleGroup k) :
    tInv (scalC a : GL ι 𝔸[k]) = scalC a⁻¹ := by
  ext i j
  simp only [tInv, MonoidHom.coe_mk, OneHom.coe_mk, scalC, ← map_inv, Units.coe_map]
  show (Matrix.scalar ι ((↑a⁻¹ : 𝔸[k])))ᵀ i j = Matrix.scalar ι ((↑a⁻¹ : 𝔸[k])) i j
  rw [Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem thetaC_scalC_eq {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (a : IdeleGroup k) :
    thetaC F (scalC a) =
      ((((ideleModule k a : ℝ) ^ Fintype.card ι)⁻¹ : ℝ) : ℂ) *
        thetaC (adelicFourierPi k F) (scalC a⁻¹) := by
  have hA := GlobalTheory.T.linearChange_mem_schwartzBruhatPi hF (scalC a : GL ι 𝔸[k])
  have h := tsum_algebraMap_eq_tsum_adelicFourierPi hA
  rw [GlobalTheory.CompanionTheory.LtrFourier.Hd.adelicFourierPi_ltr, tInv_scalC, det_scalC] at h
  have e1 : thetaC F (scalC a) =
      ∑' ξ : ι → k, ltr (scalC a : GL ι 𝔸[k]) F (fun i => algebraMap k 𝔸[k] (ξ i)) := rfl
  have e2 : thetaC (adelicFourierPi k F) (scalC a⁻¹) =
      ∑' ξ : ι → k, ltr (scalC a⁻¹ : GL ι 𝔸[k]) (adelicFourierPi k F) (fun i => algebraMap k 𝔸[k] (ξ i)) := rfl
  rw [e1, h, e2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [tsum_mul_left]
  congr 1
  rw [map_pow]
  simp only [Positive.val_pow, Complex.ofReal_pow, Complex.ofReal_inv]

end GlobalTheory.CompanionTheory.EpsteinRankN.Hd
