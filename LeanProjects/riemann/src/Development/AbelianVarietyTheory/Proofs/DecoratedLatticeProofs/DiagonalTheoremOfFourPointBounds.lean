import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinrankLeRankOnAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbstractDiagonalBoundCollisionsCountedOnceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramPoincareHilbertSchmidtDeviationLeSplitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqualIdentificationPairPriceLeSixFifthsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWordsStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section
namespace GlobalTheory.Core.Diag
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exp_neg_le_two_fifths {x : ℝ} (hx : 2 ≤ x) : Real.exp (-x) ≤ 2 / 5 * Real.exp (-x / 2) := by
  have h2 : Real.exp (-x / 2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h1 : Real.exp (-1) < 2 / 5 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have e : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem diag_arith {H N₁ N₂ P s dd d E₂ E Γ₁ Γ₂ Γ : ℝ} (hH : H ≤ 3 / 2 * N₁ + 3 * N₂)
    (h₁ : N₁ ≤ 2 * P * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd)) (h₂ : N₂ ≤ d * E) (hP : P ≤ 6 / 5)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hdd : 0 ≤ dd) (hd : 0 ≤ d) (hE₂ : 0 ≤ E₂) (hE : E ≤ 2 / 5 * E₂)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂) (hΓ : Γ₁ + Γ₂ ≤ Γ) :
    H ≤ 4 * ((Γ + 1) * dd + d * E₂) + 2 * d * E := by
  have hS : 0 ≤ s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd := by positivity
  have p1 : 2 * P * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd) ≤ 2 * (6 / 5) * (s * dd + E₂ * d + Γ₁ * dd + Γ₂ * dd) :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  have p2 : s * dd ≤ dd := mul_le_of_le_one_left hdd hs1
  have p3 : (Γ₁ + Γ₂) * dd ≤ Γ * dd := mul_le_mul_of_nonneg_right hΓ hdd
  have p4 : d * E ≤ d * (2 / 5 * E₂) := mul_le_mul_of_nonneg_left hE hd
  nlinarith

theorem sDiagAt_of_points : ∀ (D : D7) (c : Formalism.L2.SG.ThmSOwn.ConcK D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ : ℝ)
    (u : D.what₂.Word), 29 ≤ C' → 29 ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 0 ≤ Γ₁ → 0 ≤ Γ₂ → Γ₁ + Γ₂ ≤ Γ →
    VanishingGramTermsBound c.Y u → CollS c.Y u →
    (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).genSet) ≤ Γ₁ * ddC c.X c.Y u u →
    (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).ngSet) ≤ Γ₂ * ddC c.X c.Y u u → SDiagAt D u Γ (1 / 2) := by
  intro D c large₂ C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ u hC' hCl h0 hg1 hg2 hg hG0 hColl hgen hng
  obtain ⟨hExp, hAbs⟩ := GlobalTheory.T.kernel_expansion_absolute_convergence_equal_words
  have hT := c.tie
  have hA : (c.Y.tO u u).AbsConv := hAbs D c.X c.Y u u hT
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 (by linarith)
  have hPg : PgC c.Y ≤ 6 / 5 := GlobalTheory.T.equalIdentificationPairPrice_le_six_fifths C' Cl Cg cb Cu cT CT C0 D large₂ c.X c.Y hK2
  have hPg0 : 0 ≤ PgC c.Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (c.Y.tO u u).GGBound (PgC c.Y) :=
    Formalism.L2.SG.TermOp.ggBound c.Y.TR (c.Y.cs u) (c.Y.cs u) (c.Y.FN u) (c.Y.FN u) Formalism.L2.SG.Closed.TermsGGBound_holds
      c.Y.psi_ne (fun v => card_ge_three hK2.2 c.Y.TR v)
  have hNE := normExpSatTied_holds D c.X c.Y u u hT
  have hK0 := GlobalTheory.T.abstractDiagonalBound_collisions_counted_once _ _ _ _ _ (c.Y.tO u u) (oneC c.X c.Y u) (PgC c.Y) _ _ _ hPg0 hA hNE.1 hNE.2 hGB
    (Formalism.L2.SG.TermOp.rowOrth c.Y.TR (c.Y.cs u) (c.Y.cs u) (c.Y.FN u) (c.Y.FN u))
    (Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds D c.X c.Y u u hT) (idOneC_holds D c.X c.Y u hT) hColl hgen hng
  have hsplit := GlobalTheory.T.gramPoincareHilbertSchmidtDeviation_le_split D u
  rw [Formalism.L2.SG.ThmSOwn.hsNormSq_diag c.hI (hExp D c.X c.Y u u hT) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u),
    Formalism.L2.SG.ThmSOwn.hsNormSq_Kpp c.hI hA] at hsplit
  have hdd : 0 ≤ ddC c.X c.Y u u := dd_nonneg hT u u
  have hdu : duC c.X c.Y u = (D.duS u : ℝ) := hT.2.2.1 u
  have hddE : ddC c.X c.Y u u = (D.duS u : ℝ) ^ 2 / D.what₂.Dstar := by
    unfold ddC; rw [hdu, hT.2.2.2.1]; ring
  have hd0 : (0 : ℝ) ≤ duC c.X c.Y u := Nat.cast_nonneg _

  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf1 : 1 ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := h0.1.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    omega
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hlog : 1 ≤ Real.log D.R.k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hx2 : 2 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k := by
    have : (5 : ℝ) * 1 * 1 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k := by gcongr
    linarith
  have hE := exp_neg_le_two_fifths hx2

  have g0 : (1 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have g1 : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).one_lt.le
  have hq : 1 ≤ Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := Real.one_le_sqrt.2 (one_le_mul_of_one_le_of_one_le g0 g1)
  have hi0 : 0 ≤ (Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have key := diag_arith hsplit hK0 hG0.2 hPg (pow_nonneg hi0 _) (pow_le_one₀ hi0 (inv_le_one_of_one_le₀ hq)) hdd hd0
    (Real.exp_pos _).le hE hg1 hg2 hg
  have e1 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) =
      Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) := by
    congr 1; ring
  unfold SDiagAt
  unfold epsK at key
  rw [hddE, hdu, e1] at key
  calc _ ≤ _ := key
    _ = _ := by ring

end GlobalTheory.Core.Diag
