import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaHStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchedFamilyMassLawBaseSituationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNormsCongrModLevelSqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericMassLeHeightPowMulGluedCountStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountConstantEqUnscaledMainConstantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormsInvariantsGenericRationalFramePairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantPowLeHaarWeightStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeightsFamPf

theorem weightsFam_of (hS : PI.VolStabS.MassDataS.SWXS) : GlobalTheory.SnFam.WeightsFam := by
  intro Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH⟩ := GlobalTheory.T.differentLocalIdentity_familiesLemmaH Cg cb Cw cT CT C0
  refine ⟨max aH 2, bH, fun C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire _hBk
    K S TS cls hFQ γ _hγ Fm hFT _hRel _hTerm hG5 => ?_⟩
  have hC' : (2 : ℝ) ≤ C' := le_trans (le_max_right _ _) e1
  have hCH : aH ≤ C' := le_trans (le_max_left _ _) e1

  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := four_rank_add_seven_le_k hc
  have hk5 : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k := by
    obtain ⟨⟨hH0, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH0
    dsimp only at hH0
    obtain ⟨-, h2, h3, -, -⟩ := hH0
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
    have hf : ((D.R.m : ℝ)) ^ 4 ≤ (D.R.f : ℝ) := by exact_mod_cast h3
    have hm5 : (2 : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hm 5
    have hm4 : (2 : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm 4
    have hmm : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 4 := by
      have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by linarith
      calc (D.R.m : ℝ) = (D.R.m : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
    have h64 : (64 : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 := by nlinarith
    have ha : 64 * (D.R.f : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) := mul_le_mul_of_nonneg_right h64 hf0
    have hb' : C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L :=
      le_mul_of_one_le_right (by nlinarith) hL
    have hreal : (D.R.m : ℝ) + (D.R.f : ℝ) + 5 ≤ (D.R.k : ℝ) := by nlinarith
    have hnat : D.R.m + D.R.f + 5 ≤ D.R.k := by exact_mod_cast hreal
    omega

  have hLaw := GlobalTheory.T.matchedFamily_mass_law_base_situation Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc K S TS cls hFQ γ Fm hFT hG5
  obtain ⟨_w0, F, F', _Y0, _hw0, _hn, _hZ, _hTP, hBase, _hML, _hgenL⟩ := id hLaw
  have hcong := GlobalTheory.T.flagNorms_congr_mod_level_sq D (zOf Y) Fm.FP u u' F F' hBase.1 (fun p => (hBase.2.1 p).2.2.2.2.2.2)

  obtain ⟨hpos, hHp, w, G', hw, hzt, hTP', hcell, hglue⟩ := GlobalTheory.T.genericMass_le_heightPow_mul_gluedCount D X Y u u' hk4 Fm γ hG5.1 hLaw
  obtain ⟨-, -, -, -, -, -, ⟨_, _, -, -, -, -, -, hLT⟩, -⟩ := hc.2.2
  obtain ⟨s, hgl, hs⟩ := GlobalTheory.T.gluedLattice_weightedCount_le_explicit D X Y u u' hLT hk5 hcong G' hzt hTP'
  obtain ⟨hne, hngen⟩ := hglue s hgl
  obtain ⟨⟨Λ, hΛ, hEZ⟩, hgs⟩ := hs hne
  obtain ⟨hfac, hAA⟩ := GlobalTheory.T.meanCountConstant_eq_unscaledMainConstant hS Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hk5 hcong hb X0 ψ hT sd C Th F0 what₂
    vR Q i0 i0' νq
  obtain ⟨hDl, hNG, hLam⟩ := GlobalTheory.T.norms_invariants_generic_rational_framePair D X Y u u' hcong G' Λ w hzt hTP' hΛ hEZ hcell
  have hHT := hH C' Cl hCH e2 D large₂ X Y u u' hc TS cls (nmlOf Y u u') γ Fm hFT
  subst hw
  have hrd : 0 < D.host.rdE := by
    unfold Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero _)
  set HP := HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts w) with hHPdef
  have hHt1 : 1 ≤ Fm.toL.Htot := by
    show 1 ≤ ∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp
    have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : {p // p ∈ Fm.P} => (1 : ℝ))
      (g := fun p => (Fm.FP p.1).Hp) (fun _ _ => zero_le_one) (fun p _ => hHp p.1 p.2)
    simpa using this
  have hH1 : 1 ≤ HP := by rw [hHT]; exact hHt1
  have hg1 : (1 : ℝ) ≤ (X.B.g : ℝ) := by
    obtain ⟨-, -, -, -, -, -, -, hg0, hg1, -⟩ := hc.2.1
    rw [X.g_eq]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg0.ne_zero hg1.ne_zero)
  have hgS : ((gS D : ℕ) : ℝ) = (X.B.g : ℝ) := by rw [X.g_eq]; rfl
  have hND0 : 0 ≤ NDPt D.host.rdE (toPts w) := by
    unfold NDPt
    exact Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity
  have hND : NDPt D.host.rdE (toPts w) ≤ HP := by
    have h1 : 1 ≤ ((X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)))⁻¹ *
        NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) := by
      have hp : 0 < (X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)) :=
        pow_pos (by linarith) _
      rw [inv_mul_eq_div, le_div_iff₀ hp, one_mul]
      calc _ ≤ (X.B.g : ℝ) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) :=
            pow_le_pow_right₀ hg1 (Nat.mul_le_mul_right _ (by omega))
        _ ≤ _ := hgS ▸ hNG
    rw [hHPdef]
    unfold HPt
    exact le_mul_of_one_le_left hND0 h1
  have hhaar := GlobalTheory.T.gram_invariant_pow_le_haar_weight D.host.E D.R.rS D.R.k (Tu D u * Tu D u') D.host.rdE HP (toPts w) hrd hDl hND
  rw [← hHT] at hngen
  have hY0 : 0 ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
    apply pow_nonneg
    exact le_trans (pow_nonneg (by positivity) _) hNG
  have hHa : 0 < HP ^ (3 * (D.R.rS + 1) ^ 2) := pow_pos (by linarith) _
  have hNle : Fm.toL.ngenTot ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) *
      (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
      NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
    calc Fm.toL.ngenTot ≤ _ := hngen
      _ ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * ((bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
          Formalism.L2.SG.MassDataConc.ngFac D) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
            (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
          rw [← hAA]; exact mul_le_mul_of_nonneg_left hgs hHa.le
      _ = _ := by rw [← mul_assoc 2, mul_assoc (2 * _), mul_comm (Formalism.L2.SG.MassDataConc.ngFac D), hLam]; ring
  have hc0 : 0 ≤ 2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
      PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f := by
    by_contra hneg
    push_neg at hneg
    have h1 : HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
        PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hHa.le hneg.le
    have h2 := mul_nonpos_of_nonpos_of_nonneg h1 hY0
    linarith
  have hnP : 0 ≤ nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts w) := by
    unfold nPt
    exact Finset.prod_nonneg fun _ _ => mul_nonneg (pow_nonneg (by positivity) _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (by positivity) _)
  have hab : 3 * (D.R.rS + 1) ^ 2 + 6 * (2 * D.R.rS + 2) ≤ PN.eN D.R.rS := by
    unfold PN.eN
    generalize (D.R.rS + 1) ^ 2 = t
    omega
  refine ⟨hpos, ?_⟩
  calc Fm.toL.ngenTot ≤ _ := hNle
    _ ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
        PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) * (HP ^ (6 * (2 * D.R.rS + 2)) *
          nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w)) :=
        mul_le_mul_of_nonneg_left hhaar (mul_nonneg hHa.le hc0)
    _ = (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
        HP ^ (3 * (D.R.rS + 1) ^ 2 + 6 * (2 * D.R.rS + 2)) *
          nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w) := by ring
    _ ≤ (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
        HP ^ PN.eN D.R.rS * nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w) := by
        gcongr
    _ = _ := by ring

end GlobalTheory.WeightsFamPf
