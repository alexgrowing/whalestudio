import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClassesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLossStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMassStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_of_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  intro hS CT C hC hCT
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hC1 : (1 : ℝ) ≤ C := by nlinarith
  obtain ⟨K₀, hK⟩ := GlobalTheory.T.corankSums_bound_with_expLoss C hC1
  refine ⟨max K₀ 4, ?_⟩
  intro D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 hC' hCl hH hCc hAbs hTie hFo hn hd
  have hK₀ : K₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'1 : (1 : ℝ) ≤ C' := by linarith [le_max_right K₀ 4]
  have hCl4 : (4 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  have hHy := Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH.2.1 hH.1 hH.2.2 (by linarith) hC'1 le_rfl u
  have hXi := GlobalTheory.T.corankSizeHypothesis_explicitConstant_siegelMass hS C hC D large₂ u u C' Cl Cg cb Cu cT CT C0 1 (by linarith) hHy
  have hP := Formalism.L2.SG.LoopsCut.params_at hH X u hCl4 hCT hC1 hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hP1 : Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
      (Cnt.NT D u) 1 := by
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, _, _⟩ := hP
    refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, le_rfl, ?_⟩
    apply Real.one_le_exp
    have hl : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hC0 : (0 : ℝ) ≤ C := by linarith
    positivity
  have hGam0 : 0 ≤ GamS D large₂ := (Real.exp_pos _).le
  have hGam8 : GamS D large₂ ≤ Real.exp ((D.R.k : ℝ) / 8) := by
    unfold GamS
    apply Real.exp_le_exp.2
    have h1 : 8 * large₂.CGam ≤ C' := hH.1.1
    have h2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.2.1
    have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
    have hM : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    nlinarith
  obtain ⟨hND, hDG⟩ := hK D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v (Cnt.NT D u) (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) hP1 hXi hGam0 hGam8
  obtain ⟨hJ, hW, hFC, _, _, _, _⟩ := hTie
  have hG := Formalism.L2.SG.LoopTieOf.gammaFixed_of_hypotheses Y hH
  have hm := Formalism.MainNotions.BridgeLemma.d_m_eq D
  have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq]; unfold gg; push_cast; ring
  have hcls : ∀ s, 2 ≤ s → s ≤ D.R.k → Formalism.L2.SG.LoopsCut.ClassLe (Y.tO u u) (Formalism.L2.SG.LoopsCut.bigS (Y.tO u u) s)
      ((fun s : ℕ => (D.duS u : ℝ) *
        (Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
                  (BridgeLemma.XiB D large₂ u C) * BridgeLemma.rDD D u +
          Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
            (BridgeLemma.XiB D large₂ u C))) s) := by
    intro s h2 hk
    have base := Formalism.L2.SG.LoopTieOf.gam_mul_le hG Z hFo
      (Formalism.L2.SG.LoopTieOf.classS_le T hJ hW hFC Z C hn hd s h2 hk)
    rw [hm, ← hg] at base
    exact base
  have habs := GlobalTheory.T.pairAbs_corank_ge_two_le_sum_corankClasses _ _ _ _ _ (Y.tO u u) D.R.k _ hAbs
    (fun p _ => Formalism.L2.SG.LoopsCut.corank_le_k Y u u p.1 p.2) hcls
  have hdd : ddC X Y u u = (D.duS u : ℝ) * BridgeLemma.rDD D u := Formalism.L2.SG.LoopTieOf.ddC_eq hCc u u
  have hdu : duC X Y u = (D.duS u : ℝ) := hCc.2.2.1 u
  have hdr0 : 0 ≤ (D.duS u : ℝ) * BridgeLemma.rDD D u := hdd ▸ dd_nonneg hCc u u
  have hd0 : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
  have hgg : ((X.B.g : ℕ) : ℝ) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by rw [X.g_eq]; push_cast; ring
  unfold CollS
  rw [hdd, hdu]
  set d : ℝ := (D.duS u : ℝ) with hdef
  set r : ℝ := BridgeLemma.rDD D u with hrdef
  set N := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hN
  set G := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hGd
  have hsum : ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) =
      d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  calc _ ≤ ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) := habs
    _ = d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := hsum
    _ ≤ d * r * (√(X.B.g : ℝ))⁻¹ ^ (D.R.k * D.R.f) +
        d * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hND hdr0) (mul_le_mul_of_nonneg_left hDG hd0)
    _ = _ := by rw [hgg]; ring

end GlobalTheory.Core.Deg
