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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ShiftRowMul

variable {D : D7}

theorem latV_at_le_all {S : HSp D} {Λ : Lat S} {v : GlobalTheory.FinPl.Pl D} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S Λ (· = v)) : y ∈ latV S Λ (fun _ => True) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at *
  refine AddSubgroup.closure_mono ?_ hy
  rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun _ h => (h trivial).elim, a, ha, x, hx, rfl⟩

theorem smul_mem_of_idLat {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0)
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {c : D.host.E} (hc : c ∈ I⁻¹) {x : Fin n → D.host.E}
    (hx : x ∈ idLat I Λ) : c • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hx
    have h1 : c * t ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hI]; exact FractionalIdeal.mul_mem_mul hc ht
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [smul_smul, ← hr, algebraMap_smul]
    exact Λ.smul_mem r hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul r x _ h =>
    rw [← algebraMap_smul D.host.E r x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Λ.smul_mem r h

theorem smul_mem_latV {S : HSp D} {Λ : Lat S} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {v : GlobalTheory.FinPl.Pl D}
    {s : AE D} (hs : s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * I⁻¹) v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S (idLat I Λ) (fun _ => True)) : s • z ∈ latV S Λ (· = v) := by
  have hAA : D.host.AA ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hs
    by_cases hI : I = 0
    · subst hI
      rw [_root_.inv_zero, mul_zero, FractionalIdeal.mem_zero_iff] at hb
      subst hb
      rw [TensorProduct.tmul_zero, zero_smul]; exact zero_mem _
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hz
      have hba : b * a ∈ I⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hb ha
        rwa [mul_comm D.host.AA⁻¹, mul_assoc, inv_mul_cancel₀ hAA, mul_one] at this
      refine AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβ hα,
        fun w hw => by rw [map_mul, hβv w hw, zero_mul], 1, rfl, (b * a) • x, smul_mem_of_idLat hI hba hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.FinPlLoc.pairA_mul, one_mul, mul_assoc]
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add s s' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | neg s _ h => rw [neg_smul]; exact neg_mem h

end GlobalTheory.ShiftRowMul

theorem GlobalTheory.AscFin.shiftRow_smul_mulVec_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * (shiftId G)⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hq T L μ0 hL sc G W Mv hMv F hF ρ h M hM v y hy s hs
  have hBig : M ∈ latBig G (2 * ρ + 1) :=
    GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W Mv hMv (2 * ρ + 1) (by omega) (by omega) hM
  have hS : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1 + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT := ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W Mv hMv F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  have hmap := ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT (fun _ => True) M).1 hBig).2 y
    (GlobalTheory.ShiftRowMul.latV_at_le_all hy)
  exact GlobalTheory.ShiftRowMul.smul_mem_latV hs hmap
