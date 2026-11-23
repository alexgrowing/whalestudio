import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeLatOSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualStandardFrameLineLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualBesselCoreVertexLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWittStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCoreVertexLatticeSplitsAlongOrthDecompositStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.GridLat

theorem lattices_grid : OnStd fun {D} _ _ {sc} {G} W F => (∀ i, i < D.R.m → FinLat (latRow G i) ∧ FinLat (latCore G i) ∧ FinLat (latBig G i) ∧ IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) ∧ (∀ ρ h, IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) ∧ (∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v ∧ MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v) ∧ IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) ∧ ∀ v, OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v) ∧ ∀ ρ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ ρ * (G.pl.stAbar sc ^ ρ)⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have sdP : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := fun i hi => (G.sp.P_is i hi).sd
  have sdShift : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    intro i hi
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' (sdG i hi) h1 h2
  have sdLine : ∀ a b : ℕ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ a * (G.pl.stAbar sc ^ a)⁻¹ *
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b *
        (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹))
      (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
    intro a b
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc a b
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' (GlobalTheory.T.isSelfDual_standardFrame_lineLattice F hF) h1 h2
  refine ⟨fun i hi => ⟨GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.chi i 0) (isSelfDualC_neg (sdG (i + 1) hi)) (sdG i hi.le),
    GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.core i) (isSelfDualC_neg (sdP (i + 1) hi)) (sdP i hi.le),
    GlobalTheory.T.isFiniteAdelicMatrixLattice_latO_selfDual _ _ _ _ (sdG (i + 1) hi) (sdShift i hi.le), sdShift i hi.le⟩,
    fun ρ h => ⟨GlobalTheory.T.isSelfDual_besselCoreVertexLattice F hF ρ h, fun v => ⟨GlobalTheory.T.bessel_vertex_lattice_splits_along_witt F hF ρ h v, GlobalTheory.T.fourierJacobiVertexLattice_splitsAlongWitt_at_place F hF ρ h v⟩, ?_, fun v => GlobalTheory.T.orthAt_oB_lat0_of_std F hF ρ h v⟩,
    fun ρ => ?_⟩
  · have := sdLine (ρ + 1) 0
    simpa only [pow_zero, inv_one, mul_one] using this
  · have := sdLine ρ 1
    simp only [pow_one] at this
    exact this

end GlobalTheory.AscFin.GridLat

end
