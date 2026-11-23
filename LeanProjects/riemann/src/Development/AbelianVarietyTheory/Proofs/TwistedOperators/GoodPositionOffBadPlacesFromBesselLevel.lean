import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardLatticeOffS0Statement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeMembershipAdjointIffStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.GoodPosBF

theorem goodPosition_offBadPlaces_from_besselLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v ∧ StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v ∧ (0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  refine ⟨⟨sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e), (I.2.1 ρ h).1,
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e),
    sd (.core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j e => by cases e),
    ((I.2.1 ρ h).2.1 v).1, ((I.2.1 ρ h).2.1 v).2,
    GlobalTheory.T.psi_primitive_standardFrames_besselLevel D hq T L μ0 hL sc G W M hM F hF ρ h v hv, GlobalTheory.T.besselLevel_columns_carry_latticeLines_offExceptional D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩,
    GlobalTheory.T.standard_lattice_off_S0 D hq T L μ0 hL sc G W M hM F hF ρ h v hv, GlobalTheory.T.lattice_membership_adjoint_iff D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩

end GlobalTheory.GoodPosBF
