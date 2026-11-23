import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiscreteSeriesDegreeBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProduct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizesStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open NumberField Finset

namespace GlobalTheory.Core.Deg.AtRecord

open Formalism.FourierDecayAlt

theorem m_eq (R : Ranks) : R.m = 2 * R.rS + 2 := by
  obtain ⟨t, ht⟩ := R.m_even
  have := R.two_le_m
  simp only [Ranks.rS]; omega

theorem sfac_cast (n : ℕ) : (Sz.sfac n : ℝ) = ∏ i ∈ range n, (i.factorial : ℝ) := by
  simp [Sz.sfac]

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < vand x :=
  prod_pos fun _ _ => prod_pos fun _ hb => sub_pos.2 (h (mem_filter.1 hb).2)

theorem isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D w τ) := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := D.R.k_even
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n, D.R.k = n + 1 := ⟨D.R.k - 1, by omega⟩
    have key : ∀ (d i : ℕ) (h : i + d + 1 < D.R.k),
        (D.hcW w τ).u ⟨i + d + 1, h⟩ < (D.hcW w τ).u ⟨i, by omega⟩ := by
      have step : ∀ (i : ℕ) (h : i + 1 < D.R.k), (D.hcW w τ).u ⟨i + 1, h⟩ < (D.hcW w τ).u ⟨i, by omega⟩ :=
        fun i h => lt_trans ((D.hcW w τ).v_gt_u ⟨i, by omega⟩) ((D.hcW w τ).u_gt_v ⟨i, by omega⟩)
      intro d
      induction d with
      | zero => intro i h; exact step i h
      | succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))
    intro i j hij
    have hlt : i.val < j.val := hij
    have := key (j.val - i.val - 1) i.val (by omega)
    have e : (D.hcW w τ).u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = (D.hcW w τ).u j :=
      congrArg _ (Fin.ext (by simp; omega))
    rw [e] at this
    unfold uS
    exact_mod_cast this
  · obtain ⟨z, hz⟩ := (D.hcW w τ).u_half a
    refine ⟨z - c + 1, ?_⟩
    unfold uS
    rw [hz, hc]; push_cast; ring

theorem tcrit_eq (D : D7) (hv : 0 < D.host.v) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Tcrit D u τ = Sz.Tcrit D.R.k D.R.m D.host.ka D.host.rdE (gg D) (VV D τ) (vand (uS D u τ)) := by
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg : 0 ≤ gg D := by unfold gg; positivity
  have hm := m_eq D.R
  have e0 : D.R.m * (D.R.m - 1) / 2 = (D.R.rS + 1) * (2 * D.R.rS + 1) := by
    have : D.R.m * (D.R.m - 1) = 2 * ((D.R.rS + 1) * (2 * D.R.rS + 1)) := by
      rw [hm, show 2 * D.R.rS + 2 - 1 = 2 * D.R.rS + 1 by omega]; ring
    omega
  have e1 : D.R.m - 1 = 2 * D.R.rS + 1 := by omega
  have hmR : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  unfold Tcrit Sz.Tcrit Sz.TcritPow
  rw [e0, e1, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hka.le]
  congr 5
  · congr 1
    rw [hmR]; push_cast; ring
  · rw [hmR]; push_cast; rw [hmR]; ring

def sizeData (D : D7) (u : D.what₂.Word) : Sz.SizeData D.what₂.Tau where
  k := D.R.k
  r := D.R.rS
  v := D.host.v
  dF := (2 * D.host.v) ^ D.R.f
  Lv := fun M => Formalism.HermitianLatticesTheory.lValEta D.host.E M
  vol := fun M => Cnt.massU D.host.E M
  g1 := D.host.g 0
  g2 := D.host.g 1
  T := (D.mem u).A.T
  dsig := D.dsig
  Vu := fun τ => vand (uS D u τ)
  du := D.duS u

theorem gaG_eq (D : D7) : gaG D = Sz.colIdx D.R.k (D.host.g 0) ^ D.R.f * Sz.colIdx D.R.k (D.host.g 1) ^ D.R.f := by
  have hS : ∀ i, StandardLattice.SplitsF D (D.host.g i) := fun i =>
    (GlobalTheory.ColClassCompare.split_g_iff D i).2 (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i)
  have hp := GlobalTheory.TypedPlacesProduct.finprod_typed_places D (fun x => ∏ i ∈ Icc 1 D.R.k, (x ^ i - 1)) hS
  have e : ∀ i, Sz.colIdx D.R.k (D.host.g i) = ∏ j ∈ Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) := fun i => by
    have : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
    unfold Sz.colIdx Sz.glCard
    rw [GlobalTheory.prod_pow_sub_pow_eq_mul_prod_Icc]
    field_simp
  rw [e, e]
  exact hp

theorem idxRows_eq (D : D7) : LocalBesselAndTopKernel.idxRows D =
    Sz.rowIdx D.R.k D.R.rS (D.host.g 0) ^ D.R.f * Sz.rowIdx D.R.k D.R.rS (D.host.g 1) ^ D.R.f := by
  have hS : ∀ i, StandardLattice.SplitsF D (D.host.g i) := fun i =>
    (GlobalTheory.ColClassCompare.split_g_iff D i).2 (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i)
  have hp := GlobalTheory.TypedPlacesProduct.finprod_typed_places D
    (fun x => LocalBesselAndTopKernel.cardGL x D.R.r / (x ^ LocalBesselAndTopKernel.dimNS D * x ^ (D.R.k * (D.R.k - 1) / 2))) hS
  have hr : D.R.k + 2 * D.R.rS + 1 = D.R.r := by have := dimS_eq D.R; omega
  unfold Sz.rowIdx
  rw [hr]
  exact hp

theorem ratio_ranks (D : D7) (hM : UnitaryVolumeMass.stMassRatio D) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (hv : 0 < D.host.v)
    (hg0 : 4 ≤ D.host.g 0) (hg1 : 4 ≤ D.host.g 1) : UnitaryVolumeMass.cTvA D := by
  intro u
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := m_eq D.R
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram
  set S := sizeData D u with hS
  have hf : S.f = D.R.f := D.what₂.card_Tau
  have hSm : S.m = D.R.m := hm.symm
  have hn : S.n = D.R.r := by
    show D.R.k + S.m - 1 = D.R.r
    rw [hSm]; rfl
  have hVu : ∀ τ, 0 < vand (uS D u τ) := fun τ => vand_pos (isHCParam_uS D u τ).1
  have hOk : S.Ok := ⟨show 1 ≤ D.R.k by omega, hv, by rw [hf]; rfl, (D.host.g_prime 0).two_le,
    (D.host.g_prime 1).two_le, (D.mem u).A.T_prime.two_le, (hst D.R.k).2.2.1, hVu⟩
  have hMR : S.MassRatios := by
    intro M h1 _
    have h1' : D.R.k < M := h1
    have h := hM M (by omega) _ _ _ _ _ _ (hst M).1 (hst (M - 1)).1 (hst M).2.1 (hst (M - 1)).2.1
    rw [StandardLattice.mass_ratio_eq] at h
    replace h := (div_eq_iff (hst (M - 1)).2.2.1.ne').1 h
    rw [hf]
    refine h.trans ?_
    unfold StandardLattice.ratioH
    rw [Real.rpow_neg (hOk.hdF ▸ by positivity), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    rfl
  have hLB : S.LBound := by
    intro M h1 _
    have h1' : D.R.k < M := h1
    rw [hf]
    exact ⟨StandardLattice.lVal_pos D M (by omega), StandardLattice.massIdentity_holds D M (by omega)⟩
  have hCC : S.ColumnCount := by
    have h := (hR _ _ _ (hst D.R.k).1).1 (hst D.R.k).2.1 u
    rw [gaG_eq, ← sfac_cast] at h
    unfold Sz.SizeData.ColumnCount Sz.SizeData.idxCol
    rw [hf]
    exact h
  have hD : S.Dstar = D.what₂.Dstar := by
    have h := (hR _ _ _ (hst D.R.r).1).2 (hst D.R.r).2.1
    rw [idxRows_eq] at h
    unfold Sz.SizeData.Dstar Sz.SizeData.idxRow
    rw [hf, hn]
    exact h.symm
  have hA := Final.sz_propA _ S hOk hMR hCC
  obtain ⟨hE0, hE⟩ := Final.sz_eaSize _ S hOk hLB (show 2 ≤ D.R.k by omega) hg0 hg1
  have hpow : ∀ τ, 0 < S.TcritPow τ ∧ (Tcrit D u τ / Tr D u) ^ D.R.k = S.TcritPow τ / (S.T : ℝ) ^ S.k := by
    intro τ
    have hrd : S.rd = D.host.rdE := by
      show 2 * (D.host.rdE / 2) = _
      ring
    have hVV : S.VV τ = VV D τ := by
      unfold Sz.SizeData.VV VV
      rw [hn, sfac_cast]; rfl
    have hpos : 0 < S.TcritPow τ := by
      have h1 : 0 < S.ka := div_pos Real.pi_pos hv
      have h2 : 0 < S.rd := mul_pos two_pos hv
      have h3 : 0 < S.g := by
        have a : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
        have b : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
        exact mul_pos a b
      have h4 : 0 < S.VV τ := by
        rw [hVV]; exact mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)
      have h5 : 0 < S.Vu τ := hVu τ
      unfold Sz.SizeData.TcritPow Sz.TcritPow
      positivity
    refine ⟨hpos, ?_⟩
    have e : Tcrit D u τ = S.TcritPow τ ^ ((1 : ℝ) / (D.R.k : ℝ)) := by
      rw [tcrit_eq D hv]
      unfold Sz.SizeData.TcritPow Sz.Tcrit
      rw [hrd, hVV, hSm]; rfl
    rw [div_pow, e, one_div, Real.rpow_inv_natCast_pow hpos.le (by omega)]
    rfl
  have hP : 0 ≤ ∏ τ, S.TcritPow τ / (S.T : ℝ) ^ S.k :=
    prod_nonneg fun τ _ => div_nonneg (hpow τ).1.le (by positivity)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ S.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num; rfl
  rw [prod_congr rfl fun τ _ => (hpow τ).2, e2, ← hD, ← hf]
  change _ ≤ S.Dstar / S.du ∧ S.Dstar / S.du ≤ _
  rw [hA]
  rw [abs_le] at hE
  refine ⟨mul_le_mul_of_nonneg_right ?_ hP, mul_le_mul_of_nonneg_right ?_ hP⟩
  · exact (Real.le_log_iff_exp_le hE0).1 hE.1
  · exact (Real.log_le_iff_le_exp hE0).1 hE.2

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

end GlobalTheory.Core.Deg.AtRecord

namespace GlobalTheory.Core.Deg

theorem smallOn_univ_unconditional : SmallOn Set.univ := by
  intro Cg cb Cu cT CT δ hcb _ hδ
  obtain ⟨t1, h1⟩ := elementary_size_bounds_of_size_hypotheses (8 / Real.log (1 + δ))
  obtain ⟨t2, h2⟩ := GlobalTheory.T.exists_threshold_criticalLevel_lower_bound cb Cu hcb
  obtain ⟨t3, h3⟩ := GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes
  refine ⟨max (max t1 t2) t3, fun C0 _ C' Cl hC' hCl D large₂ hT hR => ?_⟩
  have hC1 : t1 ≤ C' := (le_max_left _ _).trans ((le_max_left _ _).trans hC')
  have hCl1 : t1 ≤ Cl := (le_max_left _ _).trans ((le_max_left _ _).trans hCl)
  have hCl2 : t2 ≤ Cl := (le_max_right _ _).trans ((le_max_left _ _).trans hCl)
  have hC3 : t3 ≤ C' := (le_max_right _ _).trans hC'
  have hCl3 : t3 ≤ Cl := (le_max_right _ _).trans hCl
  have hVV : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ)) := fun hH0 =>
    h3 D large₂ C' Cl Cg cb Cu cT CT hC3 hCl3 hT hH0.1 (rowColumnShape_of_windowData_width_ge_one D C0 hH0.2.2 hH0.2.1)
  refine ⟨?_, ?_, ?_, fun hH0 => h2 D large₂ C' Cl Cg cT CT C0 hCl2 (hVV hH0) hH0,
    fun hH0 u => AtRecord.form_of_ranks D hR u (GlobalTheory.Mass.RowsRawMass.main D u) hH0.2.1⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (AtRecord.isHCParam_uS D w τ)).1 H _ hg
  · intro _ w τ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (AtRecord.isHCParam_uS D w τ)).2
  · intro hH0 w
    obtain ⟨-, -, -, hk, hrd, -⟩ := h1 D large₂ C' Cl Cg cb Cu cT CT hC1 hCl1 hH0.1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH0.1
    have hkR : (5 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      have := D.R.two_le_m
      exact_mod_cast (by omega : 5 ≤ D.R.k)
    have hrdv : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
    have hb : 1 ≤ large₂.sc.b := by linarith
    have h4 : (4 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
      le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
    have hg0' : 4 ≤ D.host.g 0 := by exact_mod_cast h4.trans hg0
    have hg1' : 4 ≤ D.host.g 1 := by exact_mod_cast h4.trans hg1
    exact tprod_mono D (AtRecord.ratio_ranks D (GlobalTheory.MassAtRecord.massRatio_at_record D) hR (by linarith)
      hg0' hg1') (AtRecord.err_le D hδ hk) w

end GlobalTheory.Core.Deg
