import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDecOfDecGapGapGe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhLocOfIntegrablePh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Formalism.LocalToGlobal.IndefiniteReal.RankZerothComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DSGapData

theorem two_mul_rkR_le {n : ℕ} (ε : Fin n → Bool) : 2 * GlobalTheory.Count.rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold GlobalTheory.Count.rkR
  omega

theorem rank_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h0
  have hq2 : (2 : ℝ) * q ≤ n := by exact_mod_cast hq
  have hn : (2 : ℝ) ≤ n := by linarith
  have e : ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hq1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    simpa using this
  have h1 : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have h2 : 120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (q : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ 120 * n := by positivity
    exact mul_le_mul_of_nonneg_left e this
  have h3 : 120 * (n : ℝ) * (q : ℝ) ^ 2 ≤ 30 * (n : ℝ) ^ 3 := by nlinarith
  have h4 : 30 * (n : ℝ) ^ 3 ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem big_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have : q = 0 := by omega
    subst this; simp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h0
  have hqn : (q : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : q ≤ n ^ 2 := by nlinarith
    exact_mod_cast this
  have hs : Real.sqrt q ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, hqn⟩
  have h1 : 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (n : ℝ) ^ 2 * n :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h2 : 40 * (n : ℝ) ^ 2 * n ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem gap_numeric' {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    GlobalTheory.Count.rkR ε = 0 ∨ 8 * Real.sqrt (GlobalTheory.Count.rkR ε) * (0 + 4 * n * GlobalTheory.Count.rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (GlobalTheory.Count.rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < GlobalTheory.Count.rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by
    have := two_mul_rkR_le ε
    exact_mod_cast (show 0 < n by omega)
  have e : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε) := by positivity
  nlinarith

theorem lamAt_gap {D : D7} (hH : HostHyp D) (τ : D.what₂.Tau) (i : ℕ) :
    ∀ j, i < j → j < D.R.r →
      100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) i - Formalism.L2.NTheta.lamAt (D.hc τ) j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hj
    have g := hH.gapR τ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · have := ih h (by omega)
      have h0 : (0 : ℚ) ≤ 100 * (D.R.r : ℚ) ^ 4 := by positivity
      linarith
    · subst h; exact g

theorem isHCParam_cast {n m : ℕ} (h : n = m) (lam : Fin m → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => lam (Fin.cast h i)) := by
  subst h; simpa using hl

theorem dsData_gap_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hH
  have hn : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq

  have hds : GlobalTheory.Count.IsDSData X.B X.dv := by
    intro v
    have e : X.B.lam v = fun i => Formalism.MainNotions.S.lamS D.R (D.hc (X.pl v)) (Fin.cast X.n_eq i) := funext (X.lam_eq v)
    refine ⟨?_, X.ds v, X.low v, ?_⟩
    · rw [e]
      exact isHCParam_cast X.n_eq _ (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))
    · obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ (X.ds v) 1 one_pos
      rw [ENNReal.coe_one, one_smul] at hd
      have hw : X.B.w v ≠ 0 := by
        intro h0
        have h1 := (X.low v).1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have e2 : X.dv v = d := Formalism.L2.SG.Pf.RowDictPf.fdegOf_eq hd hw
      rw [e2]
      exact hd

  have hgap : GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
    intro v a b hab
    have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (by rw [Fin.ext h])
    rw [X.lam_eq, X.lam_eq, Formalism.IndefR.ModelConjugation.lamS_eq, Formalism.IndefR.ModelConjugation.lamS_eq]
    simp only [Fin.val_cast]
    rcases lt_or_gt_of_ne hne with h | h
    · have g := lamAt_gap hH (X.pl v) a b h (by have := b.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inl g')
    · have g := lamAt_gap hH (X.pl v) b a h (by have := a.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inr (by linarith))

  have hh : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      100 * (D.R.r : ℝ) ^ 4 := by
    intro v
    rw [← hn]
    exact rank_bound _ _ (two_mul_rkR_le _)
  have hbig : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) := by
    intro v
    rw [← hn]
    exact big_bound _ _ (two_mul_rkR_le _)

  have hD := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) :=
    GlobalTheory.Dec.locDec_of_decGap_gapGe hD X.B X.dv _ hds hgap hh
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj X.B X.dv _ hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric' _ _ (hh v)
  have hph : Integrable (GlobalTheory.Count.ph X.B X.dv) (GlobalTheory.Dec.muInf X.B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  have hph' : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) := hph
  exact ⟨hds, hloc, hbig, hh, hph', GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hph'⟩

end GlobalTheory.DSGapData
