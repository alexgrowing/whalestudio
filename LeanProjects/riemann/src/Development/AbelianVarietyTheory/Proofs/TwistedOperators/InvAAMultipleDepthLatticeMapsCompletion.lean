import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAAUnit

variable {D : D7}

theorem idem_smul_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (v : GlobalTheory.FinPl.Pl D)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨GlobalTheory.FinPlLoc.ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ w) (hαi w)
    · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold GlobalTheory.FinPlLoc.idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem smul_mulVec_mem_latV : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hOff T L μ0 hL sc G W Mv hM F hF ρ h M hMr v y hy s hs
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hO : M ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 2) 0) : Set _)
      (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) :=
    GlobalTheory.RowLoc.mem_latO_negSp.1 hMr.1
  have hyT : y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) := GlobalTheory.FinPl.PsiUnit.latV_mono trivial hy
  have hA : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hV hO hyT
  have hy' : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPlLoc.latV_idAt hy i)
  have hAv : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
    rw [← hy', Matrix.mulVec_smul]
    exact idem_smul_latA v hA
  exact (((GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v).2.2.2.2.2.2 _ _ _).1 hAv).2 s hs

end GlobalTheory.AscFin.RowAAUnit

end
