import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLatticesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPiecesMutualAnnihilatorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilatorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCorePieceNonzeroVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplitsStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem piecesFB_is_and_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.T.jacobi_to_bessel_pieces_finite_adelic_lattices D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.fourierJacobiToBessel_pieces_mutual_annihilators D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨b1, b2⟩ := GlobalTheory.T.jacobi_to_bessel_pieces_mutual_annihilators D hq T L μ0 hL sc G W M hM F hF σ h h'
  exact ⟨⟨f1, g1, f2, f3, g2, g3, b1, b2, GlobalTheory.T.genericCharacter_trivial_fourierJacobi_step D hq T L μ0 hL sc G W M hM F hF σ h h', f4, GlobalTheory.T.jacobi_to_bessel_core_piece_nonzero_vacuum D hq T L μ0 hL sc G W M hM F hF σ h h'⟩,
    GlobalTheory.T.fourierJacobiToBessel_lattice_splits D hq T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin
