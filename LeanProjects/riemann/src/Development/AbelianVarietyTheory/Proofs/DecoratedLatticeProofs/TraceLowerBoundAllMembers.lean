import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobalRowsOfSizeParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NodesOfSizeData
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DuWinThreeOfCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThrEAddOneLt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.LevLow

theorem cloudUnit_lower {x eps k f CD cD : ℝ} (hx : 1 ≤ x) (he : eps ≤ 1) (hk0 : 0 ≤ f) (hfk : f ≤ k)
    (hk : k ≤ x ^ (5 : ℝ)) (hCD : 0 ≤ CD) (hc : 11 * CD ≤ cD) :
    (k * f * x ^ eps) ^ CD ≤ ((⌈x ^ cD⌉₊ : ℕ) : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hk0' : 0 ≤ k := le_trans hk0 hfk
  have h1 : x ^ eps ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx he
  have h2 : k * f ≤ x ^ (5 : ℝ) * x ^ (5 : ℝ) := mul_le_mul hk (le_trans hfk hk) hk0 (by positivity)
  have h3 : k * f * x ^ eps ≤ x ^ (11 : ℝ) := by
    have : x ^ (11 : ℝ) = x ^ (5 : ℝ) * x ^ (5 : ℝ) * x ^ (1 : ℝ) := by
      rw [← Real.rpow_add' hx0 (by norm_num), ← Real.rpow_add' hx0 (by norm_num)]; norm_num
    rw [this]
    exact mul_le_mul h2 h1 (by positivity) (by positivity)
  calc (k * f * x ^ eps) ^ CD ≤ (x ^ (11 : ℝ)) ^ CD := Real.rpow_le_rpow (by positivity) h3 hCD
    _ = x ^ (11 * CD) := by rw [← Real.rpow_mul hx0]
    _ ≤ x ^ cD := Real.rpow_le_rpow_of_exponent_le hx hc
    _ ≤ _ := Nat.le_ceil _

theorem Dstar_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar = StandardLattice.massI X.toD7 X.toD7.R.r * StandardLattice.idxSig X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) *
      ∏ τ, X.toD7.dsig τ := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem admissibleRanks_of_mass_formula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.massI D D.R.r * StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ) :
    LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
      (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]

theorem eventually_le_trace : EvP fun _ K => ∀ β : BPt K, LocalBesselAndTopKernel.FamilyMidVolume β.D → (∀ u, GlobalTheory.Core.Rk.RankMu β.D u) →
    ∀ u : β.D.what₂.Word, β.O.L.sc.b ^ ((1 / 2 : ℝ) * (β.D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr β.D u := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨max c1 (11 * 40), fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch hch
  obtain ⟨x2, hNo⟩ := GlobalTheory.Diag.PG.NodeParameters.nodes_of_parameters eps he he52
  obtain ⟨x3, hP⟩ := GlobalTheory.T.diagonal_hypotheses_of_rows_and_window GlobalTheory.Mass.siegelMassRatio_holds GlobalTheory.DsigSize.dsigHC eps 40 he he52 (by norm_num)
    (8 * C.CGam) 40 (C.P.CYL + 1) 0 le_rfl le_rfl
  refine ⟨max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)), fun K hK hx β hAdm hMu => ?_⟩
  obtain ⟨hC, hcD', hch', heps, -⟩ := hK
  have hsc : β.O.L.sc = K.s := β.sc
  have hx' : max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)) ≤ β.O.L.sc.x := by rw [hsc]; exact hx
  have hse : β.O.L.sc.eps = eps := by rw [hsc]; exact heps
  have hv : Val C cD ch β.O.L := by
    rw [show C = K.C from hC.symm, show cD = K.cD from hcD'.symm, show ch = K.ch from hch'.symm]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx') hv
    (GlobalTheory.Plug.hostArith_bpt β)
  have hx1 : 1 < β.O.L.sc.x := β.O.L.sc.one_lt_alt
  have hX : max 2 (5 / (eps / 100)) ≤ S.XX β.O.L := by
    unfold S.XX szTh
    rw [hse]
    have h0 : (0 : ℝ) ≤ max 2 (5 / (eps / 100)) := le_trans (by norm_num) (le_max_left _ _)
    have hp : 0 < eps / 100 := by positivity
    have hyP : (max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹ ≤ β.O.L.sc.x :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx'
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hyP hp.le
    rwa [Real.rpow_inv_rpow h0 hp.ne'] at this
  have G0 := GlobalTheory.Diag.PG.Model0.globalRows_of_sizeData β.O.L N.params N.sizes ((le_max_left _ _).trans hX)
    (by unfold szTh; rw [hse]; exact (le_max_right _ _).trans hX) N.params.CCount N.params.CCount_pos le_rfl
  have e2 : N.params.CYL = C.P.CYL := congrArg (fun l : List ℝ => l.getD 19 0) N.params_K
  rw [hse, e2] at G0
  have hDel : ((β.D.s.Del : ℚ) : ℝ) = ((⌈β.O.L.sc.x ^ cD⌉₊ : ℕ) : ℝ) := by
    rw [hv.Del_eq]; unfold Delv; push_cast; rfl
  have hDl : ((β.D.R.k : ℝ) * (β.D.R.f : ℝ) * β.O.L.sc.x ^ eps) ^ (40 : ℝ) ≤ ((β.D.s.Del : ℚ) : ℝ) := by
    rw [hDel]
    exact cloudUnit_lower hx1.le (by linarith) (by positivity) G0.nums.fk G0.nums.k_hi (by norm_num)
      (le_trans (le_max_right _ _) hcD)
  have G : GlobalTheory.Diag.PG.Glob0 β.D β.O.L.sc.x eps 40 (C.P.CYL + 1) :=
    ⟨⟨G0.nums.m_lo, G0.nums.mf, G0.nums.fk, G0.nums.k_lo, G0.nums.k_hi, G0.nums.lrd_lo, G0.nums.lrd_hi, hDl,
      G0.nums.Del_hi⟩, G0.g_win, G0.gap, G0.cloud, G0.off, G0.rd_lo⟩
  have hNd := hNo β.D β.O.L N.params N.sizes hse (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx')
  have hL : β.O.L.sc.L = β.O.L.sc.x ^ eps := by rw [← hse]; rfl
  have h8 : 8 * β.O.L.CGam ≤ 8 * C.CGam := by rw [N.CGam_eq]
  have hW : GlobalTheory.Diag.PG.DuWin β.D 3 := GlobalTheory.Diag.PG.duWin_three_of_count β.D (fun u' => by
    have h := hMu u'
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    exact h)
  obtain ⟨⟨-, hHS, -⟩, -, -, -⟩ := hP β.O.L.sc.x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx') β.D β.O.L
    hL h8 β.p.pt.xa.ties hAdm G hNd hW
  have hH := GlobalTheory.Core.Deg.hypL_of hHS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -, -⟩ := hH
  exact fun u => (hT u).1

theorem levelPrime_lower_at_points : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  intro hL p
  have hA : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
    RowE.of_all fun _ K β _ b _ _ _ =>
      admissibleRanks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_mass K β.X β.c.isOver β.c.dsig_eq)
  exact (EvP.and (RowE.and hA (GlobalTheory.Fam.MemberCount.member_rankMu hL p)) eventually_le_trace).mono
    fun _ _ _ H β hq c b hl => H.2 β (H.1 β hq c b hl).1 (H.1 β hq c b hl).2

end GlobalTheory.Core.LevLow

end
