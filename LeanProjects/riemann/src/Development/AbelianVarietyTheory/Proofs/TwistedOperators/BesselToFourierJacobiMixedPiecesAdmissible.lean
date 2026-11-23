import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpenStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBFiniteAdelicLatticesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BidualityDepthLatticePieceBesselStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBMutualAnnihilatorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCorePieceFiniteNonzeroVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplitsStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBF

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem symplO_neg_right' (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = - symplO S T x y := by
  have := symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right'] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ann_of_mem {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) {a' : Mx D W.rank ρ}
    (ha' : a' ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₂) :
    ∀ a ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := by
  intro a ha
  induction ha' using AddSubgroup.closure_induction with
  | mem b hb => exact hb.2 a ha
  | zero => rw [map_zero, symplO_zero_right', AddChar.map_zero_eq_one]
  | add b c _ _ hb hc => rw [map_add, symplO_add_right', AddChar.map_add_eq_mul, hb, hc, one_mul]
  | neg b _ hb => rw [map_neg, symplO_neg_right', AddChar.map_neg_eq_inv, hb, inv_one]

end GlobalTheory.PcBF

namespace GlobalTheory.PcBF

theorem pieces_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨⟨GlobalTheory.T.finite_lattice_standard_parabolic D hD T L μ0 hL sc G W M hM F hF ρ h, ⟨?_, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
    (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).2, ?_, ?_,
    (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).2,
    GlobalTheory.T.genericCharacter_trivial_besselStep_unitriangular D hD T L μ0 hL sc G W M hM F hF ρ h, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
    GlobalTheory.T.besselToFourierJacobi_depthLattice_splits D hD T L μ0 hL sc G W M hM F hF ρ h⟩
  · intro a' ha'
    induction ha' using AddSubgroup.closure_induction with
    | mem b hb => exact hb.1
    | zero => intro i j; simp only [Matrix.zero_apply]; exact zero_mem _
    | add b c _ _ hb hc => intro i j; simp only [Matrix.add_apply]; exact add_mem (hb i j) (hc i j)
    | neg b _ hb => intro i j; simp only [Matrix.neg_apply]; exact neg_mem (hb i j)
  · intro a ha
    exact ⟨fun h1 a' h2 => ann_of_mem _ _ _ _ _ h2 a h1, GlobalTheory.T.biduality_depth_lattice_piece_bessel_step D hD T L μ0 hL sc G W M hM F hF ρ h a ha⟩
  · intro a' ha'
    exact ⟨fun h2 a h1 => ann_of_mem _ _ _ _ _ h2 a h1, fun H => AddSubgroup.subset_closure ⟨ha', fun a h1 => H a h1⟩⟩

end GlobalTheory.PcBF
