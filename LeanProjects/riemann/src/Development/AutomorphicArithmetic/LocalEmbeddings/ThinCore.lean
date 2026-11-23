import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPhiHatIndPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorPointwiseBoundOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegralityBoundOfFamilyContainingScaledThetaRul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBlockProductMemIntegralHarmonic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinset
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.ContDiffAtOfDiff

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.RawThetaSup GlobalTheory.BlockTh

noncomputable section

namespace UpperTheory.Dv.Thin

section Level

variable {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
  {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r}

set_option maxHeartbeats 1000000 in

theorem theta_sup_le (hLw : Laws D j Xo c U dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hDom : Dom a n) [StarRing (𝓞 D.host.E)] {nab : NabV Xo c} (hnab : IsNab Xo c nab) {xx : Fin n → Dw.La}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) {f : Rul Xo c} (hf : IsThRule Xo c nab xx P f)
    (hc : f ∈ cuspW Xo c U (wtZ a n)) {L κ ρ : ℝ} (hL : 1 ≤ L) (hrn : D.R.r ≤ n) (hM : Real.log l.M ≤ 30 * L)
    (hrdL : Real.log (rdE D.host.E) ≤ 3 * L) (hfr : Real.log (D.R.f * D.R.r) ≤ L)
    (hdκ : ((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) ≤ κ) (hnκ : (D.R.f : ℝ) * D.R.r * n ≤ 2 * κ) (hsz : Real.log κ ≤ 20 * L)
    (hρ : ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ ρ) (z : FPt (U σ).X) :
    Real.exp (-(((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) *
      ptN (laU (U σ) a n) (rdU (U σ) f) ⟨z.1, z.2.1⟩ ≤ ρ * Real.exp (9000 * ((D.R.f : ℝ) * D.R.r * L) ^ 2 * κ) := by
  have hρ0 : 0 ≤ ρ := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hρ
  have hfin := GlobalTheory.SupDict.finrank_host D
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; omega
  have hf1 : 1 ≤ D.R.f := by have := Module.finrank_pos (R := ℚ) (M := D.host.E); omega
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hfrn : (0 : ℝ) < (D.R.f : ℝ) * D.R.r * n := by
    have : 0 < D.R.f * D.R.r * n := Nat.mul_pos (Nat.mul_pos hf1 hr1) (hr1.trans hrn)
    exact_mod_cast this
  have hd1 := GlobalTheory.SupDict.one_le_dE D.host.E
  have hrd1 : 1 ≤ rdE D.host.E := Real.one_le_rpow hd1 (by positivity)
  have hhol := (mem_cuspW.1 hc).2 σ hσ
  rw [modelWt_wtZ] at hhol
  have hle : ptN (laU (U σ) a n) (rdU (U σ) f) ⟨z.1, z.2.1⟩ ≤ supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) :=
    (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hhol)).1
      (le_iSup (fun q : FPt (U σ).X => ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a n q.1)
        (rdU (U σ) f q.1) q.2)) z)
  refine (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le).trans ?_
  rcases (supN_nonneg (U σ).X (laU (U σ) a n) (rdU (U σ) f)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; positivity
  have hx := GlobalTheory.SupDict.xiR_pos D
  have habs : absA Dw a = Formalism.L2.Pj.DF Dw a := rfl
  obtain ⟨k, xf, hort, hhalf, hla⟩ := half_sup_at_ortho hLw hσ (laU (U σ) a n) (w := 3 * κ) (by linarith)
    (fun k => (GlobalTheory.LamSpread.sum_spread_laU_le D j _ _ _ _ _ _ _ hLw σ hσ a n k).trans (by
      rw [habs, hfd]; push_cast; linarith))
    (hLw.chiTriv σ hσ a n hDom) hhol hpos
  have he2 : 2 ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hpow : ∀ (x : ℝ) (m : ℕ), 0 < x → Real.log x ≤ m * L → x ≤ Real.exp L ^ m := fun x m h1 h2 => by
    rw [← Real.exp_nat_mul]; exact (Real.log_le_iff_le_exp h1).1 h2
  have hM0 : (0 : ℝ) < l.M := by have := l.three_le; exact_mod_cast (by omega : 0 < l.M)
  have hdd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hrde := hpow (rdE D.host.E) 3 (by linarith) (by exact_mod_cast hrdL)
  have hep : (Real.exp L ^ 57)⁻¹ ≤ epsLev D.host.E D.host.d l.M (3 * κ) := by
    refine inv_pow_le_epStar he2 hM0 (hpow _ 30 hM0 (by exact_mod_cast hM)) (Real.sqrt_pos.2 hdd)
      (hpow _ 3 (Real.sqrt_pos.2 hdd) ?_) (Nat.cast_nonneg _) ?_ (by linarith) ?_
    · have h1 : Real.log D.host.d ≤ 2 * Real.log (rdE D.host.E) := GlobalTheory.NormSum.Compare.log_d_le D
      rw [Real.log_sqrt hdd.le]
      push_cast
      linarith
    · rw [hfd]
      have h1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
      have h2 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
      have := hpow (D.R.f * D.R.r) 1 (by positivity) (by simpa using hfr)
      rw [pow_one] at this
      nlinarith
    · have := hpow κ 20 (by linarith) (by exact_mod_cast hsz)
      linarith
  have hlam : ((Real.exp L ^ 40)⁻¹) ^ 2 ≤ ((U σ).X k).firstMinimumSq xf.1 := by
    refine le_trans ?_ hla
    rw [le_div_iff₀ (by positivity)]
    have h1 : 1 ≤ Real.exp L ^ 17 := one_le_pow₀ (by linarith)
    calc ((Real.exp L ^ 40)⁻¹) ^ 2 * rdE D.host.E ^ 2
        ≤ ((Real.exp L ^ 40)⁻¹) ^ 2 * ((Real.exp L ^ 3) ^ 2 * Real.exp L ^ 17) :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by linarith) hrde 2).trans
            (le_mul_of_one_le_right (by positivity) h1)) (by positivity)
      _ = (Real.exp L ^ 57)⁻¹ := by field_simp
      _ ≤ _ := by
          have : 0 < (Real.exp L ^ 57)⁻¹ := by positivity
          linarith
  have hv := GlobalTheory.Dict.ThetaPt.theta_bound_ortho GlobalTheory.chartIndependence_unconditional D.host.E H Dw l Xo c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (U σ)) hσ (hLw.unf σ hσ) hr1 (2 * xiR D) (by linarith)
    (fun k τ => congrArg (2 * ·) (hLw.xiAbs σ hσ k τ.1)) a n hDom _ nab hnab xx P hP f hf k xf hort _ (by positivity) hlam
  rw [hfd] at hv
  have hrdv : rdU (U σ) f k xf.1 = Formalism.L2.PjFree.toC (evR Xo c f ((U σ).un k xf)) := dif_pos xf.2
  rw [hrdv] at hhalf
  have key := numbers D.R.f D.R.r n _ 1 L _ _ _ 1 _ ρ _ _ hL hf1 hr1 hrn hdκ hnκ hsz hfr hrd1 hrdL (by linarith)
    zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _) hρ0 (Nat.one_le_pow _ _ (Nat.succ_pos _))
    (by simpa using hρ) hpos hhalf (hv.trans_eq (one_mul _).symm)
  rwa [one_mul] at key

theorem exists_large {ι : Type} [Fintype ι] [Nonempty ι] (u : ι → ℝ) (hu : ∀ q, 0 ≤ u q) {M A : ℝ} {d N : ℕ} (hM : 1 ≤ M)
    (hN : (Fintype.card ι : ℝ) = M ^ N) (hS : 0 < M ^ d * ∑ q, u q ^ 2)
    (h : -Real.log (Real.sqrt (M ^ d * ∑ q, u q ^ 2)) ≤ A) :
    ∃ q, Real.exp (-(A + (d + N) * Real.log M)) ≤ u q := by
  obtain ⟨q, -, hq⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  refine ⟨q, ?_⟩
  have h1 : ∑ q, u q ^ 2 ≤ M ^ N * u q ^ 2 := by
    rw [← hN, ← Finset.card_univ, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun q' _ => pow_le_pow_left₀ (hu q') (hq q' (Finset.mem_univ _)) 2
  have hM0 : 0 < M := by linarith
  have h2 : Real.sqrt (M ^ d * ∑ q, u q ^ 2) ≤ M ^ (d + N) * u q := by
    refine Real.sqrt_le_iff.2 ⟨mul_nonneg (by positivity) (hu q), ?_⟩
    calc M ^ d * ∑ q, u q ^ 2 ≤ M ^ d * (M ^ N * u q ^ 2) := by gcongr
      _ = M ^ (d + N) * u q ^ 2 := by ring
      _ ≤ (M ^ (d + N)) ^ 2 * u q ^ 2 := by
          gcongr
          exact le_self_pow₀ (one_le_pow₀ hM) two_ne_zero
      _ = _ := by ring
  have h3 : Real.exp (-A) ≤ Real.sqrt (M ^ d * ∑ q, u q ^ 2) :=
    (Real.le_log_iff_exp_le (Real.sqrt_pos.2 hS)).1 (by linarith)
  have h4 : Real.exp ((d + N) * Real.log M) = M ^ (d + N) := by
    rw [← Nat.cast_add, Real.exp_nat_mul, Real.exp_log hM0]
  rw [neg_add, Real.exp_add, Real.exp_neg ((d + N) * _), h4, mul_inv_le_iff₀' (by positivity)]
  exact h3.trans h2

set_option maxHeartbeats 1000000 in

theorem theta_lower (hLw : Laws D j Xo c U dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hDom : Dom a n) [StarRing (𝓞 D.host.E)] {nab : NabV Xo c} (hnab : IsNab Xo c nab) (α : 𝓞 D.host.E)
    (hα : α * H.bar α = (l.M : 𝓞 D.host.E)) (hMb : l.Mb = Ideal.span {H.bar α})
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (hB : IsBlockProd P) (hdeg : P.totalDegree = Formalism.L2.Pj.DF Dw a)
    {g : (Fin n → LevQ Dw l) → Rul Xo c} (hg : ∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P (g q))
    (hs : ∀ q, g q ∈ sec Xo c a n) {R0 : ℝ} {m : ℕ} (hrun : GlobalTheory.EtaAn.RunOK D.host.E D.R.r (Formalism.L2.Pj.DF Dw a) l.M R0 m)
    (hm : Dw.q ≤ m) {tableLineDegreeFive cc : ℝ} (hP14 : p14 D.host.E D.R.r n m ≤ tableLineDegreeFive)
    (hcc : 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := D.host.E) m : ℝ) ^ 4 * I2.RR (E := D.host.E) / l.M ≤ cc)
    (k : (U σ).Comp) (x : Frame ((U σ).X k).Ψ D.R.r) (hx : x ∈ ((U σ).X k).dom) :
    ∃ q, Real.exp (-(tableLineDegreeFive * (Formalism.L2.Pj.DF Dw a : ℕ) +
        cc * (2 * (I2.PT.f D.host.E : ℝ) / (I2.PT.rd D.host.E ^ 2 * ((U σ).X k).la1 x ^ 2)) +
        ((Formalism.L2.Pj.DF Dw a : ℕ) + (D.R.f * D.R.r * n : ℕ)) * Real.log l.M)) ≤
      Real.exp (-(((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) *
        ptN (laU (U σ) a n) (rdU (U σ) (g q)) ⟨k, x⟩ := by
  classical
  have hUn := hLw.unf σ hσ
  obtain ⟨b, -, hbd, hbo, -, hphi, hpn⟩ := GlobalTheory.AnVal.exists_ortho_frame D.host.E D.R.r ((U σ).X k) x hx
  obtain ⟨T, Pr, hTr, hq, hPm, hph, hbound⟩ := GlobalTheory.ThetaLower.thetaRule_sum_lower GlobalTheory.chartIndependence_unconditional
    D.host.E H Dw l Xo c σ D.R.r (U σ) k ⟨_, hbd⟩ (xiR D) nab hnab hσ hUn (hLw.unTest σ hσ k _) hbo (hLw.xiAbs σ hσ k)
    α hα hMb a n P hP hB R0 m (hdeg ▸ hrun) (Or.inr hm)
  have hxR := GlobalTheory.SupDict.xiR_pos D
  have hM1 : (1 : ℝ) ≤ l.M := by have := l.three_le; exact_mod_cast (by omega : 1 ≤ l.M)
  have hfin := GlobalTheory.SupDict.finrank_host D
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; omega
  obtain ⟨hfinQ, hcard⟩ := GlobalTheory.card_levQ D.host.E H Dw l
  haveI : Fintype (Fin n → LevQ Dw l) := Fintype.ofFinite _
  have hN : (Fintype.card (Fin n → LevQ Dw l) : ℝ) = (l.M : ℝ) ^ (D.R.f * D.R.r * n) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun, hcard, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, hfd,
      ← hUn.1]
    push_cast
    rfl
  have hb := hbound g hg
  rw [finsum_eq_sum_of_fintype] at hb
  set lie := Real.exp (-(((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) with hlie
  have hl : lie ^ 2 = ((Real.pi * (2 * xiR D))⁻¹) ^ P.totalDegree := by
    have hp : 0 < Real.pi * (2 * xiR D) := by positivity
    rw [hlie, hdeg, ← Real.exp_nat_mul, ← Real.exp_log (inv_pos.2 hp), ← Real.exp_nat_mul, Real.log_inv]
    congr 1
    push_cast
    ring
  have hval : ∀ q, ptN (laU (U σ) a n) (rdU (U σ) (g q)) ⟨k, x⟩ = ‖toC (evR Xo c (g q) ((U σ).un k ⟨_, hbd⟩))‖ :=
    fun q => (hpn _ _ (hUn.2.2.2.2.1 a n hDom (g q) (hs q) k)).trans (congrArg norm (dif_pos hbd))
  have hkey : (Real.pi⁻¹) ^ P.totalDegree * Pr.Jbound n ≤
      (l.M : ℝ) ^ Formalism.L2.Pj.DF Dw a * ∑ q, (lie * ptN (laU (U σ) a n) (rdU (U σ) (g q)) ⟨k, x⟩) ^ 2 := by
    simp only [hval, mul_pow, hl]
    rw [← Finset.mul_sum, ← hdeg]
    calc (Real.pi⁻¹) ^ P.totalDegree * Pr.Jbound n
        = (l.M : ℝ) ^ P.totalDegree * (((Real.pi * (2 * xiR D))⁻¹) ^ P.totalDegree *
            ((2 * xiR D / l.M) ^ P.totalDegree * Pr.Jbound n)) := by
          rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
          congr 2
          field_simp
      _ ≤ _ := by gcongr
  have hfin := GlobalTheory.AnVal.neg_log_sqrt_le_of_jbound D.host.E T P.totalDegree n Pr _ tableLineDegreeFive cc hkey
    (by rw [hTr, hPm]; exact hP14) (by rw [hPm, hq]; exact hcc)
  have hcc0 : 0 ≤ cc := le_trans (by unfold I2.RR I2.PT.rd; positivity) hcc
  have hφ : Pr.ph ≤ 2 * (I2.PT.f D.host.E : ℝ) / (I2.PT.rd D.host.E ^ 2 * ((U σ).X k).la1 x ^ 2) := by
    rw [hph, hphi]
    unfold I2.phiFD
    split_ifs
    · exact le_rfl
    · positivity
  refine exists_large _ (fun q => mul_nonneg (Real.exp_pos _).le (by rw [hval]; exact norm_nonneg _)) hM1 hN
    (lt_of_lt_of_le (mul_pos (by positivity) (Formalism.L2.Pj.I2FramePointLemmas.jbound_pos T Pr n)) hkey) (hfin.trans ?_)
  rw [← hdeg]
  gcongr

theorem thetaDegreeConst_le_three_mul_cube (E : Type) [Field E] [NumberField E] [IsCMField E] (r n m : ℕ) {b : ℝ} (hb : 1000 ≤ b) (hr : (r : ℝ) ≤ b)
    (hn : (n : ℝ) ≤ b) (hd : (I2.dstar (E := E) m : ℝ) ≤ 2 * b) : p14 E r n m ≤ 3 * b ^ 3 := by
  unfold p14
  have hd0 : (0 : ℝ) ≤ (I2.dstar (E := E) m : ℝ) := Nat.cast_nonneg _
  generalize (I2.dstar (E := E) m : ℝ) = d at hd hd0
  have h1 : Real.log Real.pi ≤ 4 := (Real.log_le_self Real.pi_pos.le).trans Real.pi_le_four
  have h2 : Real.log 24 ≤ 24 := Real.log_le_self (by norm_num)
  have h3 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have h4 : d / 2 * Real.log (2 * d) ≤ b * (4 * b) :=
    (mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) (by linarith)).trans
      (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
  have h5 : (n : ℝ) * (Real.log 24 + d / 2 * Real.log (2 * d)) ≤ b * (24 + b * (4 * b)) :=
    (mul_le_mul_of_nonneg_left (add_le_add h2 h4) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hn (by positivity))
  have h6 : ((r : ℝ) + 2) * Real.log 2 ≤ (b + 2) * 2 :=
    mul_le_mul (by linarith) h3 (Real.log_nonneg (by norm_num)) (by linarith)
  have h7 : 1000 * b ≤ b ^ 2 := by rw [sq]; gcongr
  have h8 : 1000 * b ^ 2 ≤ b ^ 3 := by rw [pow_succ' b 2]; gcongr
  nlinarith

theorem cc_le {b n m d R M : ℝ} (hb : 1000 ≤ b) (hn0 : 0 ≤ n) (hm0 : 0 ≤ m) (hd0 : 0 ≤ d) (hR0 : 0 ≤ R) (hn : n ≤ b)
    (hm : m ≤ b) (hd : d ≤ 2 * b) (hR : R ≤ b) (hM : b ^ 16 ≤ M) :
    8100 * Real.pi * n * m ^ 4 * d ^ 4 * R / M ≤ 1 / 2500 := by
  have hb0 : 0 < b := by linarith
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hM)]
  have h1 : 8100 * Real.pi * n * m ^ 4 * d ^ 4 * R ≤ 8100 * 4 * b * b ^ 4 * (2 * b) ^ 4 * b := by
    gcongr
    exact Real.pi_le_four
  have h2 : (1000 : ℝ) ^ 6 * b ^ 10 ≤ b ^ 6 * b ^ 10 := by gcongr
  have h3 : 0 ≤ b ^ 10 := by positivity
  nlinarith

theorem loss_le {b φ d N lM z : ℝ} (hb : 1000 ≤ b) (hφ : b ^ 14 ≤ φ) (hd0 : 0 ≤ d) (hd : d ≤ b ^ 2) (hN0 : 0 ≤ N) (hN : N ≤ b)
    (hM0 : 0 ≤ lM) (hM : lM ≤ 70 * b) (hz0 : 0 ≤ z) (hz : z ≤ b * (3 * b)) :
    d * b + 9000 * z ^ 2 * b ^ 2 + (3 * b ^ 3 * d + 1 / 2500 * φ + (d + N) * lM) ≤ φ / 1250 := by
  have hb1 : 1 ≤ b := by linarith
  have h1 : d * b ≤ b ^ 2 * b := by gcongr
  have h2 : 9000 * z ^ 2 * b ^ 2 ≤ 9000 * (b * (3 * b)) ^ 2 * b ^ 2 := by gcongr
  have h3 : 3 * b ^ 3 * d ≤ 3 * b ^ 3 * b ^ 2 := by gcongr
  have h4 : (d + N) * lM ≤ (b ^ 2 + b ^ 2) * (70 * b) := by
    gcongr
    exact hN.trans (le_self_pow₀ hb1 two_ne_zero)
  have h5 : b ^ 3 ≤ b ^ 6 := pow_le_pow_right₀ hb1 (by norm_num)
  have h6 : b ^ 5 ≤ b ^ 6 := pow_le_pow_right₀ hb1 (by norm_num)
  have h7 : (1000 : ℝ) ^ 8 * b ^ 6 ≤ b ^ 8 * b ^ 6 := by gcongr
  have h8 : 0 ≤ b ^ 6 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in

theorem core_ratio (hLw : Laws D j Xo c U dict) (α : 𝓞 D.host.E) (hα : α * H.bar α = (l.M : 𝓞 D.host.E))
    (hMb : l.Mb = Ideal.span {H.bar α}) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hDom : Dom a n) (hLP : LastPos Dw a)
    {b : ℝ} (hb : 1000 ≤ b) (hrn : D.R.r ≤ n) (hcol : D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * n)
    (hfrn : (D.R.f : ℝ) * D.R.r * n ≤ b) (hrd : D.host.rdE ^ 7 ≤ b) (hM1 : b ^ 16 ≤ l.M) (hM2 : (l.M : ℝ) ≤ b ^ 70)
    (hDF : ((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) ≤ b ^ 2) {R0 : ℝ}
    (hrun : GlobalTheory.EtaAn.RunOK D.host.E D.R.r (Formalism.L2.Pj.DF Dw a) l.M R0 D.R.m) (hm : Dw.q ≤ D.R.m)
    {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp) (x : Frame ((U σ).X k).Ψ D.R.r) (hx : x ∈ ((U σ).X k).dom)
    (hs : (l.M : ℝ) * ((U σ).X k).firstMinimumSq x ≤ 1) :
    ∃ f ∈ cuspW Xo c U (wtZ a n), rdU (U σ) f k x ≠ 0 ∧ ∀ z : FPt (U σ).X,
      Real.exp (-(2 * (I2.PT.f D.host.E : ℝ) / (I2.PT.rd D.host.E ^ 2 * ((U σ).X k).la1 x ^ 2) / 1250)) *
        ptN (modelWt (U σ) (wtZ a n)) (rdU (U σ) f) ⟨z.1, z.2.1⟩ ≤ ptN (modelWt (U σ) (wtZ a n)) (rdU (U σ) f) ⟨k, x⟩ := by
  have hci := GlobalTheory.chartIndependence_unconditional
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond D.host.E H Dw l Xo c
  have hpq : D.R.r = Dw.p + Dw.q := (hLw.unf σ hσ).1
  have ef := hostSize_f D
  have hf1 : 1 ≤ D.R.f := by
    have := GlobalTheory.SupDict.finrank_host D
    have := Module.finrank_pos (R := ℚ) (M := D.host.E)
    omega
  have hr1 : 1 ≤ D.R.r ∧ D.R.m ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  obtain ⟨P, hP, hB, hdeg, hl1⟩ := GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA D.host.E H Dw l c a n hDom.1
    (by rw [ef, ← hpq]; exact hcol)
  choose g hg hgs using fun q : Fin n → LevQ Dw l =>
    (GlobalTheory.thetaRule_exists_and_eval hci D.host.E H Dw l Xo c nab hnab a n (fun i => levRep (q i)) P hP).1
  have hcusp : ∀ q, g q ∈ cuspW Xo c U (wtZ a n) := fun q => by
    rw [cuspW_wtZ, ← Formalism.L2.PjFree.cusp_ofPj]
    exact GlobalTheory.Dict.thInCusp_cusp hci D.host.E H Dw l Xo c D.R.r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr1.1
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj _).2 (hLw.unf σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))) nab hnab a n hDom hLP
      _ ⟨_, _, hP, hg q⟩
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hr1.1.trans hrn
  have hmR : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast hr1.2
  have hb1 : 1 ≤ b := by linarith
  have hfr : (D.R.f : ℝ) * D.R.r ≤ b := (le_mul_of_one_le_right (by positivity) hnR).trans hfrn
  have hrb : (D.R.r : ℝ) ≤ b := (le_mul_of_one_le_left (by positivity) hfR).trans hfr
  have hnb : (n : ℝ) ≤ b := (le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hfR hrR)).trans hfrn
  have hd : (I2.dstar (E := D.host.E) D.R.m : ℝ) ≤ 2 * b := by
    have e : (I2.dstar (E := D.host.E) D.R.m : ℝ) = 2 * ((I2.PT.f D.host.E : ℝ) * D.R.m) := by
      unfold I2.dstar; push_cast; ring
    rw [e, ef]
    have : (D.R.f : ℝ) * D.R.m ≤ D.R.f * D.R.r := by gcongr
    linarith
  have hrd1 : 1 ≤ D.host.rdE :=
    show 1 ≤ rdE D.host.E from Real.one_le_rpow (GlobalTheory.SupDict.one_le_dE D.host.E) (by positivity)
  have hrdb : D.host.rdE ≤ b := (le_self_pow₀ hrd1 (by norm_num)).trans hrd
  have hRR : I2.RR (E := D.host.E) = D.host.rdE ^ 7 := by unfold I2.RR; rw [hostSize_rd]
  obtain ⟨q, hq⟩ := theta_lower hLw hσ hDom hnab α hα hMb hP hB hdeg hg hgs hrun hm
    (thetaDegreeConst_le_three_mul_cube D.host.E D.R.r n D.R.m hb hrb hnb hd)
    (cc_le hb (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by rw [hRR]; positivity) hnb (hmR.trans hrb) hd
      (hRR ▸ hrd) hM1) k x hx
  have hlb1 : 1 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlb : Real.log b ≤ b := Real.log_le_self (by linarith)
  have hM0 : (1 : ℝ) ≤ l.M := (one_le_pow₀ hb1).trans hM1
  have hlM : Real.log l.M ≤ 70 * Real.log b := by
    have := Real.log_le_log (by linarith) hM2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hρ : ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ Real.exp ((Formalism.L2.Pj.DF Dw a : ℕ) * b) := by
    refine (hl1 σ).trans ?_
    rw [Real.exp_nat_mul, ← hpq]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp b]) _
  have hla := ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom ((U σ).X k) hr1.1 hx
  have hsq : ((U σ).X k).la1 x ^ 2 = ((U σ).X k).firstMinimumSq x := Real.sq_sqrt (MinimumGrowthBounds.minimumSq_nonneg _ hx)
  have hφ : b ^ 14 ≤ 2 * (I2.PT.f D.host.E : ℝ) / (I2.PT.rd D.host.E ^ 2 * ((U σ).X k).la1 x ^ 2) := by
    rw [← hsq] at hs
    rw [hostSize_rd, ef, le_div_iff₀ (by positivity)]
    calc b ^ 14 * (D.host.rdE ^ 2 * ((U σ).X k).la1 x ^ 2) ≤ b ^ 14 * (b ^ 2 * ((U σ).X k).la1 x ^ 2) := by gcongr
      _ = b ^ 16 * ((U σ).X k).la1 x ^ 2 := by ring
      _ ≤ l.M * ((U σ).X k).la1 x ^ 2 := by gcongr
      _ ≤ _ := by linarith
  have hloss := loss_le (N := (D.R.f * D.R.r * n : ℕ)) (lM := Real.log l.M) (z := (D.R.f : ℝ) * D.R.r * (3 * Real.log b))
    hb hφ (Nat.cast_nonneg _) hDF (Nat.cast_nonneg _) (by push_cast; exact hfrn) (Real.log_nonneg hM0) (by linarith)
    (by positivity) (by gcongr)
  rw [modelWt_wtZ]
  refine ⟨g q, hcusp q, fun h0 => ?_, fun z => ?_⟩
  · have e : ptN (laU (U σ) a n) (rdU (U σ) (g q)) ⟨k, x⟩ = 0 := by
      unfold ptN Data.pnorm
      rw [h0, norm_zero, zero_mul]
    rw [e, mul_zero] at hq
    exact absurd hq (not_le.2 (Real.exp_pos _))
  · have hz := theta_sup_le hLw hσ hDom hnab hP (hg q) (hcusp q) (L := 3 * Real.log b) (κ := b ^ 2) (by linarith) hrn
      (by linarith) ((Real.log_le_log (show 0 < D.host.rdE by linarith) hrdb).trans (by linarith))
      ((Real.log_le_log (by positivity) hfr).trans (by linarith)) hDF (by nlinarith)
      (by rw [Real.log_pow]; push_cast; linarith) hρ z
    refine le_of_mul_le_mul_left ?_ (Real.exp_pos (-(((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))))
    rw [mul_left_comm]
    refine (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le).trans (le_trans ?_ hq)
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)

end Level

end UpperTheory.Dv.Thin
