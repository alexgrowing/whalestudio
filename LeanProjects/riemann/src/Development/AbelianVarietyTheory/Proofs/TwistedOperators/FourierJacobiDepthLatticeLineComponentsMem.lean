import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreEmbeddingMulVecMemLatticeOfSplitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreProjectionMemLatticeOfSplitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSummandProjectionMemLatticeOfSplitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineFB

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  obtain ⟨-, hfr, hline⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hx := AddSubgroup.mem_comap.1 hu
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply] at hx
  have hSc : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (G.isV (X := .core (2 * (σ + 1) + 1)) (by simp [Node.InRange]; omega) (fun j e => Node.noConfusion e)).sd
  have hSg : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.isV (X := .grid (2 * (σ + 1) + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hTg : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hℓ := (hfr σ h').2.2.1
  have hℓ' := hline (σ + 1)
  have h0 := (hfr σ h').1
  have hj : ∀ y ∈ G.Λ (.core (2 * (σ + 1) + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * (σ + 1) + 1) 0) :=
    GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hSg) fun v => ((hfr (σ + 1) h).2.1 v).2
  have hq : ∀ t ∈ G.Λ (.grid (2 * σ + 2) 0), ((F.oB σ h').qB * (F.dB σ h').q0) *ᵥ t ∈
      idLat (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    intro t ht
    rw [← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hℓ) (hfr σ h').2.2.2 _
      (GlobalTheory.T.q0_mulVec_mem_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions h0) (fun v => ((hfr σ h').2.1 v).1) t ht)
  have key : ((F.oB σ h').resT _ u).2 =
      rat ((F.oB σ h').qB * (F.dB σ h').q0) * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * rat (F.dJ (σ + 1) h).i₀ := by
    rw [OrthDec.resT_apply, rat_mul]
    change _ = (F.oB σ h').pB * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (F.dB σ h').p0, HypDec.p0_j0, Matrix.one_mul, HypDec.p0_j0, Matrix.mul_one]
  rw [key]
  have hz := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual hSg hSc hℓ _ _ hj hq _ (latO_negSp_le' _ _ _ _ _ hx.1)
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hd := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom G.modul _ ((F.oB σ h').qB * (F.dB σ h').q0) hj hq _ (hx.2 e he)
  refine GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hD μ0 hL G _ _ _ hSc hℓ hℓ' _ hz ⟨e, he, ?_⟩
  rwa [Matrix.mul_smul, Matrix.smul_mul] at hd

end GlobalTheory.LineFB

end
