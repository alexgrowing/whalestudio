import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunNum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm Formalism.BasicNotions.LevelStarExponents

variable {D : D7}

theorem dim_pos (D : D7) (j : ℕ) : (1 : ℝ) ≤ WeightFamilies.dimY D j := by
  have hf : 0 < D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hp : 2 ≤ (D.R.sigW j).1 := by unfold Ranks.sigW; simp only; omega
  have h3 : 2 * 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) := Nat.mul_le_mul hp (by omega)
  have : 0 < WeightFamilies.dimY D j := by
    unfold WeightFamilies.dimY
    apply Nat.mul_pos hf
    omega
  exact_mod_cast this

theorem dim_le (large₂ : SizeData₂ D) {j : ℕ} (hj : InR D j) : (WeightFamilies.dimY D j : ℝ) ≤ zBase large₂ ^ 2 := by
  have hs : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
    have h1 := hj.1
    have h2 := hj.2
    unfold Ranks.sigW Ranks.r; simp only; omega
  have h : WeightFamilies.dimY D j ≤ D.R.f * D.R.r ^ 2 := by
    unfold WeightFamilies.dimY
    apply Nat.mul_le_mul_left
    rw [← hs]
    generalize (D.R.sigW j).1 = p
    generalize (D.R.sigW j).2 = q
    have a : p * (p - 1) / 2 ≤ p * p := (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have b : q * (q - 1) / 2 ≤ q * q := (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    nlinarith [Nat.zero_le (p * q)]
  have h' : (WeightFamilies.dimY D j : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by exact_mod_cast h
  have m := mono large₂ 1 2 0 2 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one] at m
  exact h'.trans m

theorem ppv_nat (large₂ : SizeData₂ D) (C : ℝ) (n : ℕ) : WeightFamilies.PPv D large₂ C (n : ℝ) = C * zBase large₂ ^ n := by
  unfold WeightFamilies.PPv; rw [Real.rpow_natCast]

theorem ppv_two (large₂ : SizeData₂ D) (C : ℝ) : WeightFamilies.PPv D large₂ C 2 = C * zBase large₂ ^ 2 := by
  exact_mod_cast ppv_nat large₂ C 2

theorem ppv_three (large₂ : SizeData₂ D) (C : ℝ) : WeightFamilies.PPv D large₂ C 3 = C * zBase large₂ ^ 3 := by
  exact_mod_cast ppv_nat large₂ C 3

theorem ppv_four (large₂ : SizeData₂ D) (C : ℝ) : WeightFamilies.PPv D large₂ C 4 = C * zBase large₂ ^ 4 := by
  exact_mod_cast ppv_nat large₂ C 4

theorem ppv_ge (large₂ : SizeData₂ D) {C A : ℝ} (hC : 1000 ≤ C) (hA : 12 ≤ A) :
    1000 * zBase large₂ ^ 12 ≤ WeightFamilies.PPv D large₂ C A := by
  unfold WeightFamilies.PPv
  have h1 := one_le_Z large₂
  have h2 : zBase large₂ ^ (12 : ℕ) ≤ zBase large₂ ^ A := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by exact_mod_cast hA)
  exact mul_le_mul hC h2 (by positivity) (by linarith)

theorem PO_nonneg (large₂ : SizeData₂ D) : 0 ≤ PO D large₂ := by
  have := one_le_L large₂
  unfold PO; positivity

theorem one_add_DF_le {j : ℕ} (w : WeightFamilies.Wt D j) : 1 + (WeightAlgebra.DF w : ℝ) ≤ w.size := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  push_cast
  have : (0 : ℝ) ≤ (D.R.f : ℝ) * max ((D.R.sigW j).2 : ℝ) 1 * D.R.r * w.n := by positivity
  linarith

theorem one_le_size {j : ℕ} (w : WeightFamilies.Wt D j) : 1 ≤ w.size := by
  have := one_add_DF_le w
  have h : (0 : ℝ) ≤ WeightAlgebra.DF w := Nat.cast_nonneg _
  linarith

theorem log_size_le (large₂ : SizeData₂ D) {j : ℕ} (w : WeightFamilies.Wt D j) {CK : ℝ} (hC : CK ≤ zBase large₂)
    (h : w.size ≤ CK * D.R.k * D.R.f * large₂.sc.b) : Real.log w.size ≤ 3 * zBase large₂ := by
  have hZ := one_le_Z large₂
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hkf : (D.R.k : ℝ) * D.R.f ≤ zBase large₂ := by
    have h1 := fr_le_Z large₂
    have h2 := k_le_r D
    have h3 := two_le_f D
    nlinarith
  have h0 : (0 : ℝ) ≤ (D.R.k : ℝ) * D.R.f := by positivity
  have h2 : CK * D.R.k * D.R.f ≤ zBase large₂ * zBase large₂ := by
    rw [mul_assoc]
    exact mul_le_mul hC hkf h0 (by linarith)
  have h3 : w.size ≤ zBase large₂ * zBase large₂ * large₂.sc.b := h.trans (mul_le_mul_of_nonneg_right h2 hb.le)
  have h4 := Real.log_le_log (by linarith [one_le_size w]) h3
  have hZ0 : 0 < zBase large₂ := by linarith
  rw [Real.log_mul (by positivity) hb.ne', Real.log_mul hZ0.ne' hZ0.ne', log_b] at h4
  have h5 := Real.log_le_self hZ0.le
  have h6 := L_le_Z large₂
  linarith

theorem obound_of_opo (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (h : OPO large₂ B) (hZ : 217 ≤ zBase large₂) :
    WeightFamilies.Obound B large₂ 1 4 := by
  have h1 := PO_le large₂
  have h2 : PO D large₂ ≤ WeightFamilies.PPv D large₂ 1 4 := by
    rw [ppv_four]
    have : 217 * zBase large₂ ^ 2 ≤ zBase large₂ ^ 2 * zBase large₂ ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith
  refine ⟨h.1.trans h2, le_trans ?_ (h.2.trans h2)⟩
  unfold WeightFamilies.rdO WeightFamilies.degO
  have hd : (0 : ℝ) < |((NumberField.discr B.KO : ℤ) : ℝ)| := by
    rw [abs_pos]; exact_mod_cast NumberField.discr_ne_zero B.KO
  rw [Real.log_rpow hd]
  apply le_of_eq; ring

theorem Gc_le {large₂ : SizeData₂ D} (Q : ParameterChoice' D large₂) (B : WeightFamilies.Prov D) (h : OPO large₂ B)
    (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) (po : ℕ) (hp : Real.log po ≤ large₂.sc.L) :
    Gc large₂ B (1009 * Zb D large₂) po ≤ 2000 * zBase large₂ ^ 2 := by
  have hZ := one_le_Z large₂
  have hL := L_le_Z large₂
  have h1 := PO_le large₂
  have h2 := lamStar_le Q hg
  have hz2 : zBase large₂ ≤ zBase large₂ ^ 2 := by nlinarith
  have h3 : max
      (Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO)
      (Real.log (Module.finrank ℚ D.host.E) +
        Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| / Module.finrank ℚ D.host.E) ≤ 434 * zBase large₂ ^ 2 := by
    refine max_le (by linarith [h.1, h.2]) ?_
    rw [finrank_E]
    have e := lrd_eq D
    unfold lrd at e
    rw [e]
    linarith [log_two_f_le large₂, log_rdE_le_scL Q]
  have h4 : 2 * (D.R.f : ℝ) * D.R.r * (lamStar D + 2 * Real.log po) ≤ 46 * zBase large₂ := by
    calc _ ≤ 2 * (D.R.f : ℝ) * D.R.r * (23 * large₂.sc.L) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by unfold zBase; ring
  have eZ : Zb D large₂ = zBase large₂ := rfl
  unfold Gc
  rw [eZ]
  linarith

theorem runBaseConstant_two_bounds {large₂ : SizeData₂ D} (Q : ParameterChoice' D large₂) {CL : ℝ} (h0 : 0 ≤ CL) (hC : CL ≤ zBase large₂) :
    0 ≤ WeightFamilies.PP0v D large₂ CL 2 ∧ WeightFamilies.PP0v D large₂ CL 2 ≤ 900 * zBase large₂ ^ 3 := by
  have h1 := growthZero_le_thirty_zBase Q
  have h2 := growthZero_nonneg large₂
  unfold WeightFamilies.PP0v at h1 h2 ⊢
  rw [Real.rpow_one, one_mul] at h1 h2
  rw [Real.rpow_two]
  refine ⟨by positivity, ?_⟩
  calc _ ≤ zBase large₂ * (30 * zBase large₂) ^ 2 :=
        mul_le_mul hC (pow_le_pow_left₀ h2 h1 2) (by positivity) (h0.trans hC)
    _ = _ := by ring

theorem nbR_le (large₂ : SizeData₂ D) {j : ℕ} (w : WeightFamilies.Wt D j)
    (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) (hn : (w.n : ℝ) ≤ zBase large₂ ^ 5)
    (hs : Real.log w.size ≤ 3 * zBase large₂) : nbR large₂ w ≤ 241 * zBase large₂ ^ 7 := by
  have hZ := one_le_Z large₂
  have hL := L_le_Z large₂
  have h1 := PO_le large₂
  have h2 := log_g_sum (L := large₂) hg
  have h3 : Real.log (1 + (WeightAlgebra.DF w : ℝ)) ≤ 3 * zBase large₂ :=
    (Real.log_le_log (by positivity) (one_add_DF_le w)).trans hs
  have h4 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have h5 : (D.R.f : ℝ) * D.R.r * w.n ≤ zBase large₂ * zBase large₂ ^ 5 :=
    mul_le_mul (fr_le_Z large₂) hn (by positivity) (by linarith)
  have h6 : (D.R.f : ℝ) * D.R.r * w.n * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + Real.log (1 + (WeightAlgebra.DF w : ℝ))) ≤
      23 * zBase large₂ ^ 7 := by
    calc _ ≤ (D.R.f : ℝ) * D.R.r * w.n * (23 * zBase large₂) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ zBase large₂ * zBase large₂ ^ 5 * (23 * zBase large₂) := mul_le_mul_of_nonneg_right h5 (by linarith)
      _ = _ := by ring
  have a := Zpow_le large₂ (a := 0) (n := 7) (by norm_num)
  have b := Zpow_le large₂ (a := 2) (n := 7) (by norm_num)
  rw [pow_zero] at a
  unfold nbR
  push_cast
  linarith

theorem thetaGeneratorArchLowerConst_le (large₂ : SizeData₂ D) {j : ℕ} (w : WeightFamilies.Wt D j) (hn : (w.n : ℝ) ≤ zBase large₂ ^ 5) :
    p14R w ≤ 35 * zBase large₂ ^ 7 := by
  have hZ := one_le_Z large₂
  have hf : I2.PT.f D.host.E = D.R.f := by
    have h : Module.finrank ℚ D.host.E = 2 * D.R.f := by exact_mod_cast finrank_E D
    unfold I2.PT.f; omega
  have hd : (I2.dstar (E := D.host.E) D.R.m : ℝ) ≤ 2 * zBase large₂ := by
    unfold I2.dstar
    rw [hf]
    push_cast
    have h1 := fr_le_Z large₂
    have h2 := m_le_r D
    have h3 := two_le_f D
    nlinarith
  have hd0 : (0 : ℝ) ≤ (I2.dstar (E := D.host.E) D.R.m : ℝ) := Nat.cast_nonneg _
  have h1 : Real.log (2 * (I2.dstar (E := D.host.E) D.R.m : ℝ)) ≤ 4 * zBase large₂ :=
    (Real.log_le_self (by positivity)).trans (by linarith)
  have h2 : (I2.dstar (E := D.host.E) D.R.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := D.host.E) D.R.m : ℝ)) ≤
      zBase large₂ * (4 * zBase large₂) :=
    (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have h3 : Real.log 24 ≤ 24 := Real.log_le_self (by norm_num)
  have h4 : Real.log Real.pi ≤ 4 := (Real.log_le_self Real.pi_pos.le).trans Real.pi_le_four
  have h5 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hz2 : 1 ≤ zBase large₂ ^ 2 := one_le_pow₀ hZ
  have h6 : (w.n : ℝ) * (Real.log 24 + (I2.dstar (E := D.host.E) D.R.m : ℝ) / 2 *
      Real.log (2 * (I2.dstar (E := D.host.E) D.R.m : ℝ))) ≤ 28 * zBase large₂ ^ 7 := by
    calc _ ≤ (w.n : ℝ) * (28 * zBase large₂ ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ ≤ zBase large₂ ^ 5 * (28 * zBase large₂ ^ 2) := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by ring
  have hr := mono large₂ 0 1 0 7 (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_one, pow_zero, mul_one, one_mul] at hr
  have h7 : ((D.R.r : ℝ) + 2) * Real.log 2 ≤ (D.R.r : ℝ) + 2 :=
    mul_le_of_le_one_right (by positivity) h5.le
  have a : 1 ≤ zBase large₂ ^ 7 := one_le_pow₀ hZ
  unfold p14R GlobalTheory.BlockTh.p14
  refine max_le (by linarith) (by linarith)

theorem lamR_le {large₂ : SizeData₂ D} (Q : ParameterChoice' D large₂) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) {CL : ℝ}
    (h0 : 0 ≤ CL) (hC : CL ≤ zBase large₂)
    (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) (hn : (w.n : ℝ) ≤ zBase large₂ ^ 5)
    (hs : Real.log w.size ≤ 3 * zBase large₂) : lamR large₂ CL w ≤ 2000000 * zBase large₂ ^ 10 := by
  have hZ := one_le_Z large₂
  have h1 := PO_le large₂
  have h2 := PO_nonneg large₂
  have h3 := dim_le large₂ hj
  have h4 := nbR_le large₂ w hg hn hs
  obtain ⟨h5, h6⟩ := runBaseConstant_two_bounds Q h0 hC
  have hD : (0 : ℝ) < (WeightFamilies.dimY D j : ℝ) + 2 := by positivity
  have hz2 : 1 ≤ zBase large₂ ^ 2 := one_le_pow₀ hZ
  have h7 : Real.log (8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂)) ≤ 236 * zBase large₂ ^ 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have a : Real.log 8 ≤ 8 := Real.log_le_self (by norm_num)
    have b := Real.log_le_self hD.le
    have c : Real.log (2 + PO D large₂) ≤ 2 + PO D large₂ := Real.log_le_self (by linarith)
    push_cast
    linarith
  have a0 : 1 ≤ zBase large₂ ^ 7 := one_le_pow₀ hZ
  have a1 := Zpow_le large₂ (a := 1) (n := 7) (by norm_num)
  have a2 := Zpow_le large₂ (a := 2) (n := 7) (by norm_num)
  have a3 := Zpow_le large₂ (a := 3) (n := 7) (by norm_num)
  have a10 : 1 ≤ zBase large₂ ^ 10 := one_le_pow₀ hZ
  rw [pow_one] at a1
  have eZ : Zb D large₂ = zBase large₂ := rfl
  unfold lamR
  rw [eZ]
  refine max_le (by linarith) ?_
  calc _ ≤ WeightFamilies.PP0v D large₂ CL 2 * (1763 * zBase large₂ ^ 7) := mul_le_mul_of_nonneg_left (by linarith) h5
    _ ≤ 900 * zBase large₂ ^ 3 * (1763 * zBase large₂ ^ 7) := mul_le_mul_of_nonneg_right h6 (by linarith)
    _ = 1586700 * zBase large₂ ^ 10 := by ring
    _ ≤ _ := by linarith

theorem runIndexConstant_le_zBase_sq {large₂ : SizeData₂ D} (Q : ParameterChoice' D large₂) (j : ℕ)
    (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) :
    PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ 6000 * zBase large₂ ^ 2 := by
  have hZ := one_le_Z large₂
  have hL := L_le_Z large₂
  have h2 := lamStar_le Q hg
  have hz2 : zBase large₂ ≤ zBase large₂ ^ 2 := by nlinarith
  have eZ : Zb D large₂ = zBase large₂ := rfl
  unfold PI4
  rw [eZ]
  have h3 : 2 * (81 * zBase large₂ ^ 2) / (WeightFamilies.dimY D j : ℝ) ≤ 2 * (81 * zBase large₂ ^ 2) :=
    div_le_self (by positivity) (dim_pos D j)
  linarith

theorem polyDom_of_pageOK : ∀ (CL : ℝ) (Cq : ℝ → ℝ → ℝ), 0 < CL → ∃ Z₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → Z₀ H.CA H.CK ≤ zBase large₂ → PageGq large₂ (gcR large₂ B) 1 4 ∧ PolyDom (j := j) D B large₂ (kR CL) H C2 A2 7 1 4 (Cq H.CA H.CK) 4 (gcR large₂ B) (phR large₂ B CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) (pdR large₂ ka) ka := by
  intro CL Cq hCL
  refine ⟨fun a b => CL + |b| + |Cq a b|, ?_⟩
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hP hZ0
  beta_reduce at hZ0
  obtain ⟨hA, hS, -, -, -⟩ := hP.hyp
  obtain ⟨Q, -⟩ := hP.page
  obtain ⟨t1, -, t3, t4, t5, t6⟩ := hP.tie
  obtain ⟨-, -, -, -, hg, -, -, hp1, hp2, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, hka, -, -, -, hnW, -, -, hL, -, hwL, hT, -, -, -, -, -, -, hO, hDom⟩ := hS
  rw [t1] at hDom
  obtain ⟨d1, d2, -, -, -, -, -, -, d9, -⟩ := hDom
  have eZ : Zb D large₂ = zBase large₂ := rfl
  rw [eZ] at d2 d9
  have hZ := one_le_Z large₂
  have hLZ := L_le_Z large₂
  have hL1 := one_le_L large₂
  have hC2 : C2 ≤ zBase large₂ := (le_self_pow₀ (by linarith) (by norm_num)).trans d2
  have hbig : 10 ^ 9 ≤ zBase large₂ := by
    refine le_trans ?_ d2
    calc (10 : ℝ) ^ 9 ≤ 1000 ^ 20 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) d1 20
  have hb := abs_nonneg H.CK
  have hq := abs_nonneg (Cq H.CA H.CK)
  have hCK : H.CK ≤ zBase large₂ := (le_abs_self _).trans (by linarith)
  have hCq : Cq H.CA H.CK ≤ zBase large₂ := (le_abs_self _).trans (by linarith)
  have hCLZ : CL ≤ zBase large₂ := by linarith
  have hn : (wL.n : ℝ) ≤ zBase large₂ ^ 5 := by
    rw [hL.1]
    calc _ ≤ C2 * zBase large₂ ^ 4 := hnW.trans d9
      _ ≤ zBase large₂ * zBase large₂ ^ 4 := mul_le_mul_of_nonneg_right hC2 (by positivity)
      _ = _ := by ring
  have hsk := log_size_le large₂ ka hCK hka
  have hsk0 : 0 ≤ Real.log ka.size := Real.log_nonneg (one_le_size ka)
  have hsL : Real.log wL.size ≤ 3 * zBase large₂ := by
    refine log_size_le large₂ wL hCK (hwL.trans (div_le_self ?_ ?_))
    · linarith [one_le_size ka]
    · exact_mod_cast hT
  have step : ∀ n : ℕ, 10 ^ 9 * zBase large₂ ^ n ≤ zBase large₂ ^ (n + 1) := fun n => by
    rw [pow_succ' (zBase large₂) n]
    exact mul_le_mul_of_nonneg_right hbig (by positivity)
  have z0 : 1 ≤ zBase large₂ ^ 2 := one_le_pow₀ hZ
  have z1 : zBase large₂ ≤ zBase large₂ ^ 2 := by simpa using Zpow_le large₂ (a := 1) (n := 2) (by norm_num)
  have z2 := Zpow_le large₂ (a := 2) (n := 4) (by norm_num)
  have z3 := Zpow_le large₂ (a := 3) (n := 4) (by norm_num)
  have z4 := Zpow_le large₂ (a := 4) (n := 5) (by norm_num)
  have z5 := Zpow_le large₂ (a := 5) (n := 7) (by norm_num)
  have z7 := Zpow_le large₂ (a := 7) (n := 10) (by norm_num)
  have z11 := Zpow_le large₂ (a := 11) (n := 12) (by norm_num)
  have s2 : 10 ^ 9 * zBase large₂ ^ 2 ≤ zBase large₂ ^ 3 := step 2
  have s10 : 10 ^ 9 * zBase large₂ ^ 10 ≤ zBase large₂ ^ 11 := step 10
  have hPP := ppv_ge large₂ d1 t6
  have hG1 : 1 ≤ gcR large₂ B := le_max_left _ _
  have hG : gcR large₂ B ≤ 2000 * zBase large₂ ^ 2 :=
    max_le (by linarith) (max_le (Gc_le Q B hO hg _ hp1) (Gc_le Q B hO hg _ hp2))
  have hPO := PO_le large₂
  have hPO0 := PO_nonneg large₂
  have hw1 : 1 ≤ prwR large₂ := by unfold prwR; linarith
  have hw : prwR large₂ ≤ 256 * zBase large₂ ^ 2 := by unfold prwR; linarith
  obtain ⟨hp0, hp⟩ := runBaseConstant_two_bounds Q hCL.le hCLZ
  have hlam := lamR_le Q hj wL hCL.le hCLZ hg hn hsL
  have hlam1 : 1 ≤ lamR large₂ CL wL := le_max_left _ _
  have hp14 := thetaGeneratorArchLowerConst_le large₂ wL hn
  have hp141 : 1 ≤ p14R wL := le_max_left _ _
  have hPN : max 1 (PN D large₂) ≤ 27 * zBase large₂ ^ 2 := by
    refine max_le (by linarith) ?_
    unfold PN; linarith [lamStar_le Q hg]
  have hPN1 : 1 ≤ max 1 (PN D large₂) := le_max_left _ _
  have hI : max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) ≤ 6000 * zBase large₂ ^ 2 :=
    max_le (by linarith) (runIndexConstant_le_zBase_sq Q j hg)
  have hI1 : 1 ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := le_max_left _ _
  have hH : phR large₂ B CL wL ≤ 5000000 * zBase large₂ ^ 10 := by unfold phR; linarith
  have hH1 : prwR large₂ ≤ phR large₂ B CL wL := by unfold phR; linarith
  have hd : pdR large₂ ka ≤ 4164 * zBase large₂ ^ 4 := by
    unfold pdR
    rw [ppv_three]
    calc _ ≤ 1041 * zBase large₂ ^ 3 * (4 * zBase large₂) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hm : WeightFamilies.PP0v D large₂ CL 2 * (1 + Real.log ka.size) ≤ 3600 * zBase large₂ ^ 4 := by
    calc _ ≤ 900 * zBase large₂ ^ 3 * (4 * zBase large₂) := mul_le_mul hp (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  have hQ : WeightFamilies.PPv D large₂ (Cq H.CA H.CK) 4 ≤ zBase large₂ ^ 5 := by
    rw [ppv_four]
    calc _ ≤ zBase large₂ * zBase large₂ ^ 4 := mul_le_mul_of_nonneg_right hCq (by positivity)
      _ = _ := by ring
  have hPP2 : 2 ≤ WeightFamilies.PPv D large₂ C2 A2 := by linarith
  have hsq : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hsqD : WeightFamilies.PPv D large₂ C2 A2 ^ 2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) :=
    le_mul_of_one_le_right (by positivity) (dim_pos D j)
  have e1 : (kR CL).CL = CL := rfl
  have e2 : (kR CL).AL = 2 := rfl
  have e3 : (kR CL).CRm = 7 := rfl
  refine ⟨?_, ?_⟩
  · unfold PageGq
    rw [ppv_four]; linarith
  · unfold PolyDom
    rw [e1, e2, e3, t3, t4, t5, ppv_two]
    refine ⟨by norm_num, by norm_num, by linarith, by linarith, hp0, obound_of_opo large₂ B hO (by linarith), le_rfl, ?_,
      by linarith, hP.ck, by linarith, by linarith, by linarith, by linarith, by linarith, hH1, by linarith, by linarith⟩
    unfold WeightFamilies.RRv
    have hr := one_le_rdE D
    have e7 : D.host.rdE ^ (7 : ℝ) = D.host.rdE ^ (7 : ℕ) := by exact_mod_cast Real.rpow_natCast D.host.rdE 7
    rw [e7, ← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ hr (by norm_num)

end GlobalTheory.RunNum
