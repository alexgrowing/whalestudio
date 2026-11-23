import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CorePiece

variable {D : D7}

theorem proj_mem_adelic_lattice_of_mono {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {z : Fin S.rank → AE D}
    (hz : z ∈ latA S L P) : d.p0 *ᵥ z ∈ latA S₀ L₀ P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.p0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.p0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact GlobalTheory.FinPl.VacFlat.smul_mem_latA ha (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mem_lattice_of_extend_inclusion {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W} {LW₀ : Lat W₀}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW₀ : IsSelfDualC W₀ LW₀)
    (hmV : ∀ v, MonoAt dV LV LV₀ v) (hmW : ∀ v, MonoAt dW LW LW₀ v) {u : WO V₀ W₀}
    (hu : dV.ext0 W (dW.inc0 V₀ u) ∈ latO V W (LV : Set _) (LW : Set _) fun _ => True) :
    u ∈ latO V₀ W₀ (LV₀ : Set _) (LW₀ : Set _) fun _ => True := by
  have hE : dV.ext0 W (dW.inc0 V₀ u) = dW.j0 * u * dV.p0 := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
  rw [hE] at hu
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hu0 : dW.p0 * (dW.j0 * u * dV.p0) * dV.j0 = u := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W₀ LV₀ LW₀ hV₀ hW₀ _ u).2 ⟨?_, fun y hy => ?_⟩
  · rw [← hu0]
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · have key : (show Matrix (Fin W₀.rank) (Fin V₀.rank) (AE D) from u) *ᵥ y =
        dW.p0 *ᵥ ((dW.j0 * u * dV.p0) *ᵥ (dV.j0 *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu0]
    rw [key]
    exact proj_mem_adelic_lattice_of_mono dW hW₀.1 (fun v _ => hmW v)
      (GlobalTheory.FinPl.LatMem.latO_maps hV hu (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace dV hV.1 (fun v _ => hmV v) hy))

theorem core_fin_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ u ∈ (pcBF W F ρ h).Γ₀, MxAt (fun _ => True) (show Mx D (G.V (.core (2 * ρ + 1))).rank (F.V₀ ρ).rank from u)) ∧
      ∃ f, VacG W.ψ (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (pcBF W F ρ h).Γ₀ f ∧ f ≠ 0 := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h
  obtain ⟨-, hB, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hOff T L μ0 hL sc G W M hM F hF
  obtain ⟨hsd0, hmono, -, -⟩ := hB ρ h
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hW₀ : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.isV (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j hj => Node.noConfusion hj)).sd
  have hle : (pcBF W F ρ h).Γ₀ ≤ latO (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (lat0 F ρ h : Set _)
      (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
    intro u hu
    refine mem_lattice_of_extend_inclusion (F.dB ρ h) (F.dJ ρ h) hV hsd0 hW₀ (fun v => (hmono v).1) (fun v => (hmono v).2) ?_
    exact GlobalTheory.RowLoc.mem_latO_negSp.1 (AddSubgroup.mem_comap.1 hu).1
  exact ⟨fun u hu => GlobalTheory.FinPl.LatMem.latO_mxAt (hle hu), GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ W.ψ_std _ _ _ _ hsd0 hW₀ _ hle⟩

end GlobalTheory.AscFin.CorePiece

end
