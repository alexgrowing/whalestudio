import Formalism.SharpRestriction.CuspSpanNormBounds.RadialChainStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
import Formalism.SharpRestriction.CuspSpanNormBounds.ChainLength
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusProjectedBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.YangianSpanCharacter.YangianRelationFirst
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FinalDS
import Formalism.FormalDegreeBessel.FinalIO
import Formalism.RealPlaceAnalysis.FinalF

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem two_le_absNorm (D : D7) (p : HeightOneSpectrum (𝓞 D.host.F)) : 2 ≤ Ideal.absNorm p.asIdeal := by
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact p.ne_bot
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact p.isPrime.ne_top
  omega

theorem sc_one_lt_L {D : D7} (large₂ : SizeData₂ D) : 1 < large₂.sc.L :=
  Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos

theorem sc_one_lt_b {D : D7} (large₂ : SizeData₂ D) : 1 < large₂.sc.b :=
  Real.one_lt_exp_iff.mpr (by linarith [sc_one_lt_L large₂])

private theorem ranks_k_lemma (R : Formalism.BasicNotions.Ranks) : 5 ≤ R.k := by
  obtain ⟨_, k, m, t, _, _, _, h2, h3, _, _, _, _, _⟩ := R
  dsimp only
  omega

private theorem ranks_all_lemma (R : Formalism.BasicNotions.Ranks) : (∃ j, R.m = j + j) ∧ 2 ≤ R.m ∧ R.m + 3 ≤ R.k := by
  obtain ⟨_, k, m, t, _, hm, _, h2, h3, _, _, _, _, _⟩ := R
  exact ⟨hm, h2, h3⟩

theorem five_le_k (D : D7) : (5 : ℝ) ≤ D.R.k := by
  exact_mod_cast ranks_k_lemma D.R

theorem one_le_log_k (D : D7) : 1 ≤ Real.log D.R.k := by
  have hk := five_le_k D
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he : Real.exp 1 ≤ (D.R.k : ℝ) := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (D.R.k : ℝ) := Real.log_le_log (Real.exp_pos 1) he

private theorem ranks_m_lemma (R : Formalism.BasicNotions.Ranks) : 2 ≤ R.m := by
  obtain ⟨_, k, m, t, _, _, _, h2, _, _, _, _, _, _⟩ := R
  dsimp only
  exact h2

theorem two_le_mR (D : D7) : (2 : ℝ) ≤ D.R.m := by
  exact_mod_cast ranks_m_lemma D.R

private theorem ranks_f_lemma (R : Formalism.BasicNotions.Ranks) : 2 ≤ R.f := by
  obtain ⟨fr, k, m, t, _, _, _, h2, _, _, _, h6, _, _⟩ := R
  show 2 ≤ 2 * fr.ord
  omega

theorem two_le_fR (D : D7) : (2 : ℝ) ≤ D.R.f := by
  exact_mod_cast ranks_f_lemma D.R

theorem sqrt_le_sq_nat (r : ℕ) : Real.sqrt (r : ℝ) ≤ (r : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0
    simp
  · have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hsq : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt (Nat.cast_nonneg r)
    nlinarith [sq_nonneg (Real.sqrt (r : ℝ) - 1), sq_nonneg ((r : ℝ) - 1), Real.sqrt_nonneg (r : ℝ)]

theorem gapC_le (D : D7) (C Cl : ℝ) (hCl : C ≤ Cl) (h25 : 0 < Cl) :
    C * D.R.k * (D.R.m : ℝ) ^ 3 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 := by
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := by linarith [five_le_k D]
  have hm : (1 : ℝ) ≤ (D.R.m : ℝ) := by linarith [two_le_mR D]
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := by linarith
  have hm3 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := pow_nonneg hm0 3
  have h1 : C * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCl hk) hm3
  have h2 : (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) ^ 4 := by
    calc (D.R.m : ℝ) ^ 3 = (D.R.m : ℝ) ^ 3 * 1 := by ring
      _ ≤ (D.R.m : ℝ) ^ 3 * (D.R.m : ℝ) := mul_le_mul_of_nonneg_left hm hm3
      _ = (D.R.m : ℝ) ^ 4 := by ring
  have h3 : (0 : ℝ) ≤ Cl * (D.R.k : ℝ) := mul_nonneg h25.le hk
  calc C * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 := h1
    _ ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h2 h3

theorem gap_all {n : ℕ} (f : Fin n → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin n) (hi : i.1 + 1 < n), G < f i - f ⟨i.1 + 1, hi⟩) :
    ∀ a c : Fin n, a ≠ c → G < |f a - f c| := by
  have step : ∀ i j : Fin n, j.1 = i.1 + 1 → G < f i - f j := by
    intro i j hij
    have hj : i.1 + 1 < n := by omega
    have e : j = ⟨i.1 + 1, hj⟩ := Fin.ext hij
    rw [e]
    exact h i hj
  have key : ∀ d : ℕ, ∀ i j : Fin n, j.1 = i.1 + d + 1 → G < f i - f j := by
    intro d
    induction d with
    | zero => intro i j hij; exact step i j (by omega)
    | succ d ih =>
      intro i j hij
      have hm : i.1 + d + 1 < n := by omega
      have h1 := ih i ⟨i.1 + d + 1, hm⟩ rfl
      have h2 := step ⟨i.1 + d + 1, hm⟩ j (by show j.1 = i.1 + d + 1 + 1; omega)
      linarith
  have G0 : ∀ i j : Fin n, i.1 < j.1 → G < f i - f j := fun i j hij =>
    key (j.1 - i.1 - 1) i j (by omega)
  intro a c hac
  have hv : a.1 ≠ c.1 := fun e => hac (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
  · have h1 := G0 a c hlt
    rw [abs_of_pos (show (0 : ℝ) < f a - f c by linarith)]
    exact h1
  · have h1 := G0 c a hgt
    rw [abs_sub_comm, abs_of_pos (show (0 : ℝ) < f c - f a by linarith)]
    exact h1

theorem klogk_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hC' : 1 ≤ C') :
    Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ (D.R.k : ℝ) * Real.log D.R.k := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25⟩ := hH
  have hL := sc_one_lt_L large₂
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hm2 := two_le_mR D
  have hk5 := five_le_k D
  have hlk := one_le_log_k D
  have hf4 : (D.R.m : ℝ) ^ 4 ≤ D.R.f := by exact_mod_cast a3
  have e0 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := mul_nonneg (by positivity) hL0
  have e1 : (D.R.m : ℝ) ^ 7 ≤ (D.R.m : ℝ) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have e2 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := mul_nonneg (by positivity) hL0
  calc Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ D.R.m * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := mul_le_mul_of_nonneg_right a24 e0
    _ = (D.R.m : ℝ) ^ 7 * large₂.sc.L := by ring
    _ ≤ (D.R.m : ℝ) ^ 9 * large₂.sc.L := mul_le_mul_of_nonneg_right e1 hL0
    _ = (D.R.m : ℝ) ^ 5 * (D.R.m : ℝ) ^ 4 * large₂.sc.L := by ring
    _ ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf4 (by positivity)) hL0
    _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := le_mul_of_one_le_left e2 hC'
    _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
    _ ≤ D.R.k := a2
    _ ≤ (D.R.k : ℝ) * Real.log D.R.k := le_mul_of_one_le_right (by linarith) hlk

theorem logf_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT A : ℝ)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hA : 1 ≤ A) :
    Real.log (D.R.f : ℝ) ^ 2 ≤ A * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ∧
      Real.log (D.R.f : ℝ) ≤ A * (D.R.rS : ℝ) ^ 2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  have hL := sc_one_lt_L large₂
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hm2 := two_le_mR D
  have hf2 := two_le_fR D
  have hlf : 0 ≤ Real.log (D.R.f : ℝ) := Real.log_nonneg (by linarith)
  constructor
  · have hr : (D.R.rS : ℝ) ≤ D.R.m := by
      have : D.R.rS ≤ D.R.m := by simp only [Ranks.rS]; omega
      exact_mod_cast this
    have e1 : Real.log (D.R.f : ℝ) ^ 2 ≤ D.R.rS := by
      calc Real.log (D.R.f : ℝ) ^ 2 ≤ Real.sqrt (D.R.rS : ℝ) ^ 2 := pow_le_pow_left₀ hlf a5 2
        _ = D.R.rS := Real.sq_sqrt (by positivity)
    have e4 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have e5 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right (by positivity) hL.le
    have e3 : 0 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := mul_nonneg (by positivity) hL0
    calc Real.log (D.R.f : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := by linarith
      _ ≤ A * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := le_mul_of_one_le_left e3 hA
  · calc Real.log (D.R.f : ℝ) ≤ (D.R.rS : ℝ) ^ 2 := a5.trans (sqrt_le_sq_nat _)
      _ ≤ A * (D.R.rS : ℝ) ^ 2 := le_mul_of_one_le_left (by positivity) hA

theorem tieSplit (D : D7) (p : ℕ) (h : SplitsE D p) : Lat.SplitsCompletely (E := D.host.E) p := h

theorem Stand_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 2 < Cl)
    (u u' : D.what₂.Word) : Cnt.Stand D u u' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25⟩ := hH
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := hD
  have hg0 := (D.host.g_prime 0).two_le
  have hg1 := (D.host.g_prime 1).two_le
  have hG : 4 ≤ D.host.g 0 * D.host.g 1 := by nlinarith
  have hG2 : 2 < (D.host.g 0 * D.host.g 1) ^ 2 := by nlinarith
  have three : ∀ w : D.what₂.Word, 3 ≤ (D.mem w).A.T := by
    intro w
    have hp := (D.mem w).A.T_prime.two_le
    by_contra hc
    have h2 : (D.mem w).A.T = 2 := by omega
    have := (d9 w).2
    rw [h2, Nat.mod_eq_of_lt hG2, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have cop : ∀ w : D.what₂.Word, Nat.Coprime (D.host.g 0 * D.host.g 1) (D.mem w).A.T := fun w =>
    (Nat.Coprime.mul_right
      ((Nat.coprime_primes (D.mem w).A.T_prime (D.host.g_prime 0)).mpr (d14 w).1)
      ((Nat.coprime_primes (D.mem w).A.T_prime (D.host.g_prime 1)).mpr (d14 w).2)).symm
  refine ⟨?_, (D.mem u).A.T_prime, (D.mem u').A.T_prime, three u, three u',
    tieSplit D _ (d9 u).1, tieSplit D _ (d9 u').1,
    D.host.g_prime 0, D.host.g_prime 1, D.host.g_ne, ?_, Nat.Coprime.mul_right (cop u) (cop u'), ?_⟩
  · have h3 : (2 : ℝ) < D.R.m := lt_of_lt_of_le hCl a24
    have h3' : 2 < D.R.m := by exact_mod_cast h3
    obtain ⟨t, ht⟩ := D.R.m_even
    simp only [Ranks.rS]
    omega
  · intro i
    fin_cases i
    · exact tieSplit D _ d11
    · exact tieSplit D _ d12
  · have e1 : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (D.host.g 0 * D.host.g 1) ^ 2] :=
      ((d9 u).2 : _ ≡ 1 [MOD _]).trans ((d9 u').2 : _ ≡ 1 [MOD _]).symm
    exact Nat.ModEq.of_dvd (dvd_pow_self _ two_ne_zero) e1

def Sizes3b (D : D7) (A : ℝ) : Prop :=
  (∀ u u' : D.what₂.Word, Tr D u / Tr D u' ≤ A) ∧
  ∀ (u u' : D.what₂.Word) (τ : D.what₂.Tau), vand (uS D u' τ) ≤ A ^ D.R.k * vand (uS D u τ)

theorem count_hypotheses_of_sizes (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A : ℝ)
    (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h0 : 1 ≤ C0) (hCl : 2 < Cl) (hC' : 1 ≤ C')
    (hA : 1 ≤ A) (hb : Sizes3b D A) (u u' : D.what₂.Word) :
    Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A :=
  ⟨⟨hH, hD, h0⟩, Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hD hH hCl u u', hb.1 u' u, hb.1 u u',
    klogk_of D large₂ C' Cl Cg cb Cu cT CT hH hC', (logf_of D large₂ C' Cl Cg cb Cu cT CT A hH hA).1,
    (logf_of D large₂ C' Cl Cg cb Cu cT CT A hH hA).2, fun τ => ⟨hb.2 u u' τ, hb.2 u' u τ⟩⟩

theorem NonGenericAndKTwoTheorems.Hyp_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h0 : 1 ≤ C0) (hC' : 1 ≤ C') :
    NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 := by
  have hk := klogk_of D large₂ C' Cl Cg cb Cu cT CT hH hC'
  refine ⟨⟨hH, hD, h0⟩, ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25⟩ := hH
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := hD
  have hnm : (0 : ℝ) ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
  have hgap := gapC_le D Cl Cl le_rfl a25
  have hG0 : 0 ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 := mul_nonneg (mul_nonneg a25.le (by positivity)) (by positivity)
  refine ⟨by linarith, ?_, ?_, ?_, a5.trans (sqrt_le_sq_nat _), ?_, D.sp.cm.cmUnram⟩
  · intro i
    fin_cases i
    · exact ⟨a12, a13⟩
    · exact ⟨a14, a15⟩
  · exact fun τ => gap_all _ _ hG0 (fun i hi => lt_of_le_of_lt (by linarith) (a22 τ i hi))
  · have := (le_div_iff₀ a25).mp a11
    linarith
  · exact fun u => ⟨(a23 u).2, Nat.Coprime.mul_right
      ((Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime 0)).mpr (d14 u).1)
      ((Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime 1)).mpr (d14 u).2)⟩

theorem LatticeIndexAndWeightTheory.Hyp_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h0 : 1 ≤ C0) (hC' : 1 ≤ C') :
    LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 :=
  NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 hD hH h0 hC'

theorem lambda_low_index_eq_neg (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (j : ℕ) (hj : j < 2 * r + 2)
    (h' : k - 1 + j < 2 * r + k + 1) : CayleySignature.lam48 k r v b ⟨k - 1 + j, h'⟩ = -b ⟨j, hj⟩ := by
  simp only [CayleySignature.lam48, Fin.val_mk]
  split_ifs with hh
  · omega
  · exact congrArg (fun x => -b x) (Fin.ext (by show k - 1 + j - (k - 1) = j; omega))

theorem sign_pattern_false_odd_offset (k r : ℕ) (i : Fin (2 * r + k + 1)) (h : CayleySignature.eps48 k r i = false) :
    k - 1 ≤ i.val ∧ (i.val - (k - 1)) % 2 = 1 := by
  simp only [CayleySignature.eps48] at h
  split_ifs at h with hh <;> simp at h <;> constructor <;> omega

theorem gap_at_least_of_low_gap (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hk : 1 ≤ k)
    (hA : StrictAnti (CayleySignature.lam48 k r v b)) (hg : CayleySignature.LowGapGe h r b) :
    Formalism.QuantumDeterminants.GapAtLeast (CayleySignature.eps48 k r) (CayleySignature.lam48 k r v b) h := by
  have key : ∀ a c : Fin (2 * r + k + 1), a < c → CayleySignature.eps48 k r a ≠ CayleySignature.eps48 k r c →
      h ≤ CayleySignature.lam48 k r v b a - CayleySignature.lam48 k r v b c := by
    intro a c hac hne
    have hacv : a.val < c.val := hac
    have hcl := c.isLt
    by_cases hc : CayleySignature.eps48 k r c = false
    · obtain ⟨c1, c2⟩ := sign_pattern_false_odd_offset k r c hc
      obtain ⟨j, hj⟩ : ∃ j, c.val = k - 1 + (j + 1) := ⟨c.val - (k - 1) - 1, by omega⟩
      have hc' : c = ⟨k - 1 + (j + 1), by omega⟩ := Fin.ext hj
      have hi : a ≤ (⟨k - 1 + j, by omega⟩ : Fin (2 * r + k + 1)) := by
        show a.val ≤ k - 1 + j
        omega
      have e1 := hA.antitone hi
      have e2 := hg ⟨j, by omega⟩ (by simp only; omega)
      rw [hc', lambda_low_index_eq_neg k r v b (j + 1) (by omega)]
      rw [lambda_low_index_eq_neg k r v b j (by omega)] at e1
      simp only at e2
      linarith
    · have ha : CayleySignature.eps48 k r a = false := by
        cases hh : CayleySignature.eps48 k r a with
        | false => rfl
        | true =>
          exfalso; apply hne; rw [hh]
          cases hh2 : CayleySignature.eps48 k r c with
          | false => exact absurd hh2 hc
          | true => rfl
      obtain ⟨a1, a2⟩ := sign_pattern_false_odd_offset k r a ha
      obtain ⟨j, hj⟩ : ∃ j, a.val = k - 1 + j := ⟨a.val - (k - 1), by omega⟩
      have ha' : a = ⟨k - 1 + j, by omega⟩ := Fin.ext hj
      have hi : (⟨k - 1 + (j + 1), by omega⟩ : Fin (2 * r + k + 1)) ≤ c := by
        show k - 1 + (j + 1) ≤ c.val
        omega
      have e1 := hA.antitone hi
      have e2 := hg ⟨j, by omega⟩ (by simp only; omega)
      rw [ha', lambda_low_index_eq_neg k r v b j (by omega)]
      rw [lambda_low_index_eq_neg k r v b (j + 1) (by omega)] at e1
      simp only at e2
      linarith
  intro a c hne
  rcases lt_trichotomy a c with hlt | heq | hgt
  · exact (key a c hlt hne).trans (le_abs_self _)
  · exact absurd (by rw [heq]) hne
  · rw [abs_sub_comm]; exact (key c a hgt hne.symm).trans (le_abs_self _)

theorem negative_count_of_sign_pattern (k r : ℕ) (hk : 1 ≤ k) : PlaceDegreeData.qOf (CayleySignature.eps48 k r) = r + 1 := by
  unfold PlaceDegreeData.qOf
  have : (Finset.univ.filter fun a => CayleySignature.eps48 k r a = false) =
      (Finset.univ : Finset (Fin (r + 1))).image
        (fun j => (⟨k - 1 + (2 * j.val + 1), by have := j.isLt; omega⟩ : Fin (2 * r + k + 1))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      obtain ⟨i1, i2⟩ := sign_pattern_false_odd_offset k r i hi
      refine ⟨⟨(i.val - (k - 1)) / 2, by have := i.isLt; omega⟩, Fin.ext ?_⟩
      simp only
      omega
    · rintro ⟨j, rfl⟩
      have h1 : ¬ (k - 1 + (2 * j.val + 1) < k - 1) := by omega
      have h2 : (k - 1 + (2 * j.val + 1) - (k - 1)) % 2 ≠ 0 := by omega
      simp [CayleySignature.eps48]
  rw [this, Finset.card_image_of_injective _ (by
    intro x y hxy
    have := congrArg Fin.val hxy
    simp only at this
    exact Fin.ext (by omega)), Finset.card_univ, Fintype.card_fin]

theorem positive_count_of_sign_pattern (k r : ℕ) (hk : 1 ≤ k) : r + 1 ≤ PlaceDegreeData.pOf (CayleySignature.eps48 k r) := by
  unfold PlaceDegreeData.pOf
  have hsub : (Finset.univ : Finset (Fin (r + 1))).image
        (fun j => (⟨k - 1 + 2 * j.val, by have := j.isLt; omega⟩ : Fin (2 * r + k + 1))) ⊆
      (Finset.univ.filter fun a => CayleySignature.eps48 k r a = true) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    simp [CayleySignature.eps48]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (by
    intro x y hxy
    have := congrArg Fin.val hxy
    simp only at this
    exact Fin.ext (by omega)), Finset.card_univ, Fintype.card_fin] at hc
  exact hc

theorem cubic_numeric_inequality (N q t M : ℝ) (hN : 0 ≤ N) (hq : 1 ≤ q) (ht : N + 5 ≤ t) (hM : N + 2 * q * t ≤ M) :
    120 * N * q ^ 2 ≤ 2 * M ^ 3 + t + 3 := by
  have ht5 : (5 : ℝ) ≤ t := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hq2 : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have hNt : N ≤ t := by linarith
  have s1 : 120 * N * q ^ 2 ≤ 120 * t * q ^ 2 := by nlinarith
  have h25 : (25 : ℝ) ≤ t ^ 2 := by nlinarith
  have ht3 : 25 * t ≤ t ^ 3 := by nlinarith
  have s2 : 120 * t * q ^ 2 ≤ 16 * t ^ 3 * q ^ 2 := by nlinarith
  have hq3 : q ^ 2 ≤ q ^ 3 := by nlinarith
  have ht3' : (0 : ℝ) ≤ t ^ 3 := by positivity
  have s3 : 16 * t ^ 3 * q ^ 2 ≤ 16 * t ^ 3 * q ^ 3 := by nlinarith
  have hqt : 0 ≤ 2 * q * t := by nlinarith
  have hM0 : 2 * q * t ≤ M := by linarith
  have s4 : (2 * q * t) ^ 3 ≤ M ^ 3 := by
    first
    | exact pow_le_pow_left hqt hM0 3
    | exact pow_le_pow_left₀ hqt hM0 3
  have s5 : 16 * t ^ 3 * q ^ 3 = 2 * (2 * q * t) ^ 3 := by ring
  nlinarith

theorem CayleySignature.second_hypothesis_of_lifting (D : D7) (h30 : PlaceDegreeData.DiscreteSeriesDecayBound D) : CayleySignature.adm2 D := by
  intro k r z c u v b hS H _ _ _ σ P hP hDS E hE X hX h hh
  obtain ⟨hk, _, _, _, _, _, hlam, _, _, t, htodd, ht5, _, hbig⟩ := hS
  set h1 : ℝ := 2 * ((CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 with hh1
  have hmax : CayleySignature.LowGapGe (max h h1) r b := fun j hj => max_le (hh j hj) (hbig j hj).le
  have hgap := gap_at_least_of_low_gap k r v b (max h h1) hk hlam.1 hmax
  have hq := negative_count_of_sign_pattern k r hk
  have hnum : 120 * ((2 * r + k + 1 : ℕ) : ℝ) *
      ((min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ max h h1 := by
    refine le_trans ?_ (le_max_right _ _)
    have hmin : ((min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) : ℕ) : ℝ) ≤ (r : ℝ) + 1 := by
      have : min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) ≤ r + 1 := by rw [hq]; exact min_le_right _ _
      exact_mod_cast this
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have e1 : ((min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
        ((r : ℝ) + 1) ^ 2 := by
      calc _ ≤ ((r : ℝ) + 1) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hmin (by norm_num)
        _ ≤ ((r : ℝ) + 1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
        _ = ((r : ℝ) + 1) ^ 2 := Real.rpow_two _
    have e2 := cubic_numeric_inequality ((2 * r + k + 1 : ℕ) : ℝ) ((r : ℝ) + 1) (t : ℝ)
      ((CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) (by positivity) hr1
      (by have : 2 * r + k + 1 + 5 ≤ t := ht5
          exact_mod_cast this)
      (by simp only [CayleySignature.rk48]; push_cast; linarith)
    calc _ ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ ≤ _ := e2
  have hone : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.REAL.Kset (CayleySignature.eps48 k r) :=
    ⟨one_mem _, by simp⟩
  have := h30 (2 * r + k + 1) (CayleySignature.eps48 k r) (CayleySignature.lam48 k r v b) hlam H (fun g => σ (P⁻¹ * g * P)) hDS E hE
    (max h h1) hgap hnum 1 X hone hX
  have hq0 : min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) = r + 1 := by
    rw [hq]; exact min_eq_right (positive_count_of_sign_pattern k r hk)
  rw [one_mul, hq0] at this
  refine this.trans ?_
  unfold PlaceDegreeData.decBound
  apply Real.exp_le_exp.mpr
  have hhs : 0 ≤ Formalism.REAL.hs X := by unfold Formalism.REAL.hs; positivity
  have hm : 0 ≤ min (Formalism.REAL.hs X) (Real.sqrt (Formalism.REAL.hs X) / Real.sqrt (2 * ((r : ℝ) + 1))) :=
    le_min hhs (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  push_cast
  nlinarith [le_max_left h h1]

theorem threshold_cubic_inequality_sign_pattern (k r t : ℕ) (hk : 1 ≤ k) (ht5 : CayleySignature.rk48 k r + 5 ≤ t) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) *
      ((min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      2 * ((CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 := by
  have hq := negative_count_of_sign_pattern k r hk
  have hmin : ((min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) : ℕ) : ℝ) ≤ (r : ℝ) + 1 := by
    have : min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) ≤ r + 1 := by rw [hq]; exact min_le_right _ _
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have e1 : ((min (PlaceDegreeData.pOf (CayleySignature.eps48 k r)) (PlaceDegreeData.qOf (CayleySignature.eps48 k r)) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      ((r : ℝ) + 1) ^ 2 := by
    calc _ ≤ ((r : ℝ) + 1) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hmin (by norm_num)
      _ ≤ ((r : ℝ) + 1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
      _ = ((r : ℝ) + 1) ^ 2 := Real.rpow_two _
  have e2 := cubic_numeric_inequality ((2 * r + k + 1 : ℕ) : ℝ) ((r : ℝ) + 1) (t : ℝ)
    ((CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) (by positivity) hr1
    (by have : 2 * r + k + 1 + 5 ≤ t := ht5
        exact_mod_cast this)
    (by simp only [CayleySignature.rk48]; push_cast; linarith)
  calc _ ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
    _ ≤ _ := e2

theorem CayleySignature.first_hypothesis_of_lifting (D : D7) (h30 : PlaceDegreeData.DiscreteSeriesLowestKTypeFormula D) : CayleySignature.adm1 D := by
  intro k r z c u v b hS H _ _ _ σ P _ hDS E hE w hw X hX
  obtain ⟨hk, _, _, _, _, _, hlam, _, _, t, _, ht5, _, hbig⟩ := hS
  have hG := gap_at_least_of_low_gap k r v b _ hk hlam.1 (fun j hj => (hbig j hj).le)
  exact h30 (2 * r + k + 1) (CayleySignature.eps48 k r) (CayleySignature.lam48 k r v b) hlam H (fun g => σ (P⁻¹ * g * P)) hDS E hE w hw _
    hG (threshold_cubic_inequality_sign_pattern k r t hk ht5) X hX

theorem FrobeniusProjectedBounds.integrality_of_commutation (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hC' : 1 ≤ C')
    (h : NonGenericAndKTwoTheorems.Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0) : FrobeniusProjectedBounds.adm3 D large₂ C' Cl Cg cb Cu cT CT C0 :=
  fun hy u => (h (NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 hy.2.1 hy.1 hy.2.2 hC') u).2

theorem AdmissibleBoundsFromSource.integrality_of_commutation (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ)
    (h : NonGenericAndKTwoTheorems.PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0) : AdmissibleBoundsFromSource.adm3 D large₂ C0 C' Cl Cg cb Cu cT CT :=
  fun hy hp => h ⟨⟨hy.2.1, hy.1, hy.2.2⟩, hp⟩

theorem AdmissibleBoundsFromSource.sizes_bound_of_log_estimates (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ)
    (h : NonGenericAndKTwoTheorems.Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0) : AdmissibleBoundsFromSource.adm5 D large₂ C0 C' Cl Cg cb Cu cT CT :=
  fun hy hp u => (h ⟨⟨hy.2.1, hy.1, hy.2.2⟩, hp⟩ u).2

theorem FrobeniusProjectedBounds.fourth_hypothesis_of_lifting (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A c : ℝ)
    (hCl : 2 < Cl) (hC' : 1 ≤ C') (hA : 1 ≤ A)
    (hb : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes3b D A)
    (h : ∀ u u', AuxiliaryNormPrimes.aux₃ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) :
    FrobeniusProjectedBounds.ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0 c :=
  fun hy u u' S hS =>
    h u u' (count_hypotheses_of_sizes D large₂ C' Cl Cg cb Cu cT CT C0 A hy.2.1 hy.1 hy.2.2 hCl hC' hA (hb hy) u u') S hS

theorem AdmissibleBoundsFromSource.restriction_dimension_of_division (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT A c : ℝ)
    (h : ∀ u u', AuxiliaryNormPrimes.aux₃ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) :
    AdmissibleBoundsFromSource.adm6 D large₂ C0 C' Cl Cg cb Cu cT CT A c :=
  fun hy u u' hp S hS => h u u' ⟨⟨hy.2.1, hy.1, hy.2.2⟩, hp⟩ S hS

theorem AdmissibleBoundsFromSource.volume_bounds_of_source (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT ep0 CV : ℝ)
    (h : LocalBesselAndTopKernel.MidVolumeChain D large₂ ep0 CV) : AdmissibleBoundsFromSource.FilteredProjectionCriterion D large₂ C0 C' Cl Cg cb Cu cT CT ep0 :=
  fun _ τ => (h τ).1

theorem AdmissibleBoundsFromSource.volume_upper_bound_of_source (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT ep0 CV : ℝ)
    (h : LocalBesselAndTopKernel.MidVolumeChain D large₂ ep0 CV) : AdmissibleBoundsFromSource.VandermondeUpperBound D large₂ C0 C' Cl Cg cb Cu cT CT CV :=
  fun _ τ => (h τ).2

theorem AdmissibleBoundsFromSource.crystalline_lift_of_theorem_c (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT CA CA' Ce : ℝ)
    (h : LocalBesselAndTopKernel.Conclusion1 D CA CA' Ce) : AdmissibleBoundsFromSource.adm9 D large₂ C0 C' Cl Cg cb Cu cT CT CA CA' Ce :=
  fun _ u u' hne => (h u u' hne).2

theorem LocalBesselAndTopKernel.local_model_admissible_of_source (D : D7) (C : ℝ)
    (hM : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
      [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E), M.OK →
      (∀ a : E, (∀ b ∈ M.R, M.psiR (a * b) = 1) ↔ a ∈ M.R) ∧
      (∀ (m : ℕ) (ZZ : M.Mat m), (Nat.card (M.Cok ZZ) : ℝ) = (M.modK (ZZ.Z.map M.R.subtype).det)⁻¹))
    (h : ThinScalesBound.aux₃ D C) : LocalBesselAndTopKernel.MLatticeCond := by
  intro F E _ _ _ _ _ _ _ M hOK
  exact ⟨(hM F E M hOK).1, (hM F E M hOK).2, (h.2.2 F E M hOK).1⟩

theorem LocalBesselAndTopKernel.top_bound_of_part_T (D : D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : LocalBesselAndTopKernel.TopKernelBoundAllLocalModels D C := h.1

theorem LocalBesselAndTopKernel.theorem_A_of_source (D : D7) (C C' : ℝ) (Vm : ValMap D.R.k D.R.rS) (h : RadialChainStatements.aux₃ D C C' 5 Vm) :
    LocalBesselAndTopKernel.admA D C C' 5 Vm := by
  first
    | exact h
    | exact fun _ => h

theorem dec_all {n : ℕ} (f : Fin n → ℝ) (h : ∀ (i : Fin n) (hi : i.1 + 1 < n), f ⟨i.1 + 1, hi⟩ < f i) :
    ∀ a c : Fin n, a < c → f c < f a := by
  have step : ∀ i j : Fin n, j.1 = i.1 + 1 → f j < f i := by
    intro i j hij
    have hj : i.1 + 1 < n := by omega
    have e : j = ⟨i.1 + 1, hj⟩ := Fin.ext hij
    rw [e]
    exact h i hj
  have key : ∀ d : ℕ, ∀ i j : Fin n, j.1 = i.1 + d + 1 → f j < f i := by
    intro d
    induction d with
    | zero => intro i j hij; exact step i j (by omega)
    | succ d ih =>
      intro i j hij
      have hm : i.1 + d + 1 < n := by omega
      have h1 := ih i ⟨i.1 + d + 1, hm⟩ rfl
      have h2 := step ⟨i.1 + d + 1, hm⟩ j (by show j.1 = i.1 + d + 1 + 1; omega)
      linarith
  intro a c hac
  exact key (c.1 - a.1 - 1) a c (by have := Fin.lt_def.mp hac; omega)

theorem vand_uS_pos (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : 0 < vand (uS D u τ) := by
  have hdec : ∀ a c : Fin D.R.k, a < c → uS D u τ c < uS D u τ a := by
    refine dec_all _ (fun i hi => ?_)
    have h1 := (D.hcW u τ).u_gt_v ⟨i.1, by omega⟩
    have h2 := (D.hcW u τ).v_gt_u ⟨i.1, by omega⟩
    have h3 : (D.hcW u τ).u ⟨i.1 + 1, hi⟩ < (D.hcW u τ).u i := lt_trans h2 h1
    simp only [uS]
    exact_mod_cast h3
  unfold vand
  exact Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => sub_pos.mpr (hdec a b (Finset.mem_filter.mp hb).2)))

theorem rdE_pos (D : D7) : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _

theorem vand_ratio_of (D : D7) (C1 : ℝ) (h : LocalBesselAndTopKernel.MassRatio₂ D C1) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    vand (uS D u' τ) ≤ C1 ^ D.R.k * vand (uS D u τ) := by
  have hk : D.R.k ≠ 0 := by have := D.R.m_add_three_le_k; omega
  have hrd := rdE_pos D
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hgg : 0 < gg D := by
    unfold gg
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    positivity
  have hVV : 0 < VV D τ := by
    unfold VV
    exact mul_pos (D.dsig_pos τ) (Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos i))
  set Y : ℝ := D.host.ka ^ (-(((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2)) *
    D.host.rdE ^ (-(((D.R.m : ℝ) - 1) / 2)) *
    gg D ^ ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) * VV D τ with hY
  have hYpos : 0 < Y :=
    mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hka _) (Real.rpow_pos_of_pos hrd _))
      (Real.rpow_pos_of_pos hgg _)) hVV
  have hv := vand_uS_pos D u τ
  have hv' := vand_uS_pos D u' τ
  have eT : ∀ w : D.what₂.Word, Tcrit D w τ = (Y / vand (uS D w τ)) ^ ((1 : ℝ) / D.R.k) := fun w => rfl
  have pw : ∀ w : D.what₂.Word, 0 < vand (uS D w τ) → Tcrit D w τ ^ D.R.k = Y / vand (uS D w τ) := by
    intro w hw
    rw [eT w, one_div]
    exact Real.rpow_inv_natCast_pow (div_pos hYpos hw).le hk
  have hTpos : 0 < Tcrit D u' τ := by rw [eT u']; exact Real.rpow_pos_of_pos (div_pos hYpos hv') _
  have hT0 : 0 ≤ Tcrit D u τ := by rw [eT u]; exact (Real.rpow_pos_of_pos (div_pos hYpos hv) _).le
  have h1 : Tcrit D u τ ≤ C1 * Tcrit D u' τ := (div_le_iff₀ hTpos).mp (h u u' τ)
  have h2 := pow_le_pow_left₀ hT0 h1 D.R.k
  rw [mul_pow, pw u hv, pw u' hv'] at h2
  have h3 : Y / vand (uS D u τ) ≤ (C1 ^ D.R.k * Y) / vand (uS D u' τ) :=
    h2.trans (le_of_eq (mul_div_assoc _ _ _).symm)
  have h4 := (div_le_div_iff₀ hv hv').mp h3
  have h5 : Y * vand (uS D u' τ) ≤ Y * (C1 ^ D.R.k * vand (uS D u τ)) := by linarith
  exact le_of_mul_le_mul_left h5 hYpos

theorem sizes_of_vandermonde_bounds (D : D7) (C1 C2 A : ℝ) (h0 : 0 ≤ C1) (h1 : C1 ≤ A) (h2 : C2 ≤ A)
    (hb : LocalBesselAndTopKernel.MassRatio₂ D C1) (hc : LocalBesselAndTopKernel.kernel_index_full_lattice D C2) : Sizes3b D A := by
  refine ⟨fun u u' => (hc u u').trans h2, fun u u' τ => ?_⟩
  have h3 := vand_ratio_of D C1 hb u u' τ
  have hv := vand_uS_pos D u τ
  have hk : C1 ^ D.R.k ≤ A ^ D.R.k := pow_le_pow_left₀ h0 h1 _
  exact h3.trans (mul_le_mul_of_nonneg_right hk hv.le)

theorem two_rS_add_two (D : D7) : 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨⟨j, hj⟩, h2, h3⟩ := ranks_all_lemma D.R
  show 2 * (D.R.m / 2 - 1) + 2 = D.R.m
  omega

def v48 (D : D7) (τ : D.what₂.Tau) : Fin (D.R.k - 1) → ℝ := fun i => ((D.hc τ).v i : ℝ)

def b48 (D : D7) (τ : D.what₂.Tau) : Fin (2 * D.R.rS + 2) → ℝ :=
  fun j => ((D.hc τ).b (Fin.cast (two_rS_add_two D) j) : ℝ)

theorem lambda_highest_weight_eq (D : D7) (τ : D.what₂.Tau) :
    CayleySignature.lam48 D.R.k D.R.rS (v48 D τ) (b48 D τ) = lamSH D.R (D.hc τ) := by
  have hm := two_rS_add_two D
  have hk := D.R.m_add_three_le_k
  funext i
  have hi := i.isLt
  by_cases h : i.val < D.R.k - 1
  · simp [CayleySignature.lam48, lamSH, lamS, v48, h]
  · have h' : i.val - (D.R.k - 1) < D.R.m := by omega
    simp [CayleySignature.lam48, lamSH, lamS, b48, h, h']

theorem epsilon_signature_eq (D : D7) : CayleySignature.eps48 D.R.k D.R.rS = epsSH D.R := by
  funext i
  simp [CayleySignature.eps48, epsSH, epsS]

theorem psiS_eq (D : D7) (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    psiS D z = psiGen D.R.k D.R.rS z
      (fun _ => ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) := by
  funext g
  simp only [psiS, Formalism.QuantumDeterminants.psi, psiGen, Formalism.QuantumDeterminants.ell, ellA, Finset.mul_sum]

theorem low_parameter_gap_eq_diff (D : D7) (τ : D.what₂.Tau) (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2) :
    b48 D τ ⟨j.val + 1, hj⟩ - b48 D τ j = bOne D τ (j.val + 1 + 1) - bOne D τ (j.val + 1) := by
  have hm := two_rS_add_two D
  have h1 : 1 ≤ j.val + 1 + 1 ∧ j.val + 1 + 1 ≤ D.R.m := ⟨by omega, by omega⟩
  have h2 : 1 ≤ j.val + 1 ∧ j.val + 1 ≤ D.R.m := ⟨by omega, by omega⟩
  simp [b48, bOne, h1, h2]
  rfl

theorem numNV (N m t : ℝ) (hN : 6 ≤ N) (hm : m ≤ N) (hm0 : 0 ≤ m) (ht : t = N + 6) :
    2 * (N + m * t) ^ 3 + t + 3 < N ^ 19 := by
  have h1 : N + m * t ≤ 3 * N ^ 2 := by subst ht; nlinarith
  have h0 : 0 ≤ N + m * t := by subst ht; nlinarith
  have h3 : (N + m * t) ^ 3 ≤ (3 * N ^ 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
  have h4 : (3 * N ^ 2) ^ 3 = 27 * N ^ 6 := by ring
  have h6 : (6 : ℝ) ^ 6 ≤ N ^ 6 := pow_le_pow_left₀ (by norm_num) hN 6
  have h13 : (6 : ℝ) ^ 13 ≤ N ^ 13 := pow_le_pow_left₀ (by norm_num) hN 13
  have h5 : t + 3 ≤ N ^ 6 := by
    have h2 : N ^ 2 ≤ N ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h22 : N + 9 ≤ N ^ 2 := by nlinarith
    subst ht; linarith
  have h19 : N ^ 19 = N ^ 6 * N ^ 13 := by ring
  have hpos : 0 < N ^ 6 := by positivity
  have h613 : (56 : ℝ) ≤ N ^ 13 := le_trans (by norm_num) h13
  have : 56 * N ^ 6 ≤ N ^ 6 * N ^ 13 := by nlinarith
  rw [h19]; nlinarith

theorem numNV' (N m t : ℝ) (hN : 6 ≤ N) (hm : m ≤ N) (hm0 : 0 ≤ m) (ht : t = N + 1800) :
    2 * (N + m * t) ^ 3 + t + 3 < N ^ 19 := by
  subst ht
  have a : m * (N + 1800) ≤ N * (N + 1800) := mul_le_mul_of_nonneg_right hm (by linarith)
  have b : 1801 * N ≤ 301 * N ^ 2 := by nlinarith
  have h1 : N + m * (N + 1800) ≤ 302 * N ^ 2 := by nlinarith
  have h0 : 0 ≤ N + m * (N + 1800) := by
    have : 0 ≤ m * (N + 1800) := mul_nonneg hm0 (by linarith)
    linarith
  have h3 : (N + m * (N + 1800)) ^ 3 ≤ (302 * N ^ 2) ^ 3 := pow_le_pow_left₀ h0 h1 3
  have h4 : (302 * N ^ 2) ^ 3 = 27543608 * N ^ 6 := by ring
  have h13 : (6 : ℝ) ^ 13 ≤ N ^ 13 := pow_le_pow_left₀ (by norm_num) hN 13
  have h55 : (6 : ℝ) ^ 5 ≤ N ^ 5 := pow_le_pow_left₀ (by norm_num) hN 5
  have h5 : N + 1800 + 3 ≤ N ^ 6 := by
    have e : N ^ 6 = N ^ 5 * N := by ring
    have : (6 : ℝ) ^ 5 * N ≤ N ^ 5 * N := mul_le_mul_of_nonneg_right h55 (by linarith)
    rw [e]; norm_num at this; linarith
  have h19 : N ^ 19 = N ^ 6 * N ^ 13 := by ring
  have hpos : 0 < N ^ 6 := by positivity
  have h613 : (55087218 : ℝ) ≤ N ^ 13 := le_trans (by norm_num) h13
  have : 55087218 * N ^ 6 ≤ N ^ 6 * N ^ 13 := by nlinarith
  rw [h19]; nlinarith

theorem uS_dec (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : StrictAnti (uS D u τ) := by
  have hdec : ∀ a c : Fin D.R.k, a < c → uS D u τ c < uS D u τ a := by
    refine dec_all _ (fun i hi => ?_)
    have h1 := (D.hcW u τ).u_gt_v ⟨i.1, by omega⟩
    have h2 := (D.hcW u τ).v_gt_u ⟨i.1, by omega⟩
    have h3 : (D.hcW u τ).u ⟨i.1 + 1, hi⟩ < (D.hcW u τ).u i := lt_trans h2 h1
    simp only [uS]
    exact_mod_cast h3
  exact fun a c hac => hdec a c hac

theorem uS_hc (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D u τ) := by
  refine ⟨uS_dec D u τ, fun a => ?_⟩
  obtain ⟨z, hz⟩ := (D.hcW u τ).u_half a
  obtain ⟨s, hs⟩ := D.R.k_even
  refine ⟨z + 1 - s, ?_⟩
  have hk : (D.R.k : ℝ) = (s : ℝ) + s := by exact_mod_cast hs
  have hu : uS D u τ a = (z : ℝ) + 1 / 2 := by simp only [uS]; rw [hz]; push_cast; ring
  rw [hu, hk]; push_cast; ring

theorem lamSH_int (D : D7) (τ : D.what₂.Tau) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    ∃ z : ℤ, lamSH D.R (D.hc τ) i = (z : ℝ) := by
  have hm := two_rS_add_two D
  have hk := D.R.m_add_three_le_k
  have hi := i.isLt
  by_cases h : i.val < D.R.k - 1
  · obtain ⟨z, hz⟩ := (D.hc τ).v_int ⟨i.val, h⟩
    exact ⟨z, by simp [lamSH, lamS, h, hz]⟩
  · have h' : i.val - (D.R.k - 1) < D.R.m := by omega
    obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i.val - (D.R.k - 1), h'⟩
    exact ⟨-z, by simp [lamSH, lamS, h, h', hz]⟩

theorem lamSH_hc (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25⟩ := hH
  have hpos : (0 : ℝ) ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 + D.R.r * (D.R.m : ℝ) ^ 10 :=
    add_nonneg (mul_nonneg (mul_nonneg a25.le (by positivity)) (by positivity)) (by positivity)
  have hdim := dimS_eq D.R
  constructor
  · have hdec := dec_all (lamSH D.R (D.hc τ)) (fun i hi => by
      have := a22 τ ⟨i.1, by omega⟩ (by simp only; omega)
      have e : lamSH D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamSH D.R (D.hc τ) i := by
        show lamS D.R (D.hc τ) ⟨i.1 + 1, _⟩ < lamS D.R (D.hc τ) ⟨i.1, _⟩
        linarith
      exact e)
    exact fun a c hac => hdec a c hac
  · intro a
    obtain ⟨z, hz⟩ := lamSH_int D τ a
    obtain ⟨s, hs⟩ := D.R.k_even
    refine ⟨z - (D.R.rS + s), ?_⟩
    have hk : (D.R.k : ℝ) = (s : ℝ) + s := by exact_mod_cast hs
    rw [hz]; push_cast; rw [hk]; ring

theorem nS_cast (D : D7) : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by
  obtain ⟨⟨j, hj⟩, h2, h3⟩ := ranks_all_lemma D.R
  have e : 2 * D.R.rS + D.R.k + 1 = D.R.r := by
    show 2 * (D.R.m / 2 - 1) + D.R.k + 1 = D.R.k + D.R.m - 1
    omega
  rw [e]

theorem six_le_n (D : D7) : (6 : ℝ) ≤ (D.R.r : ℝ) := by
  obtain ⟨⟨j, hj⟩, h2, h3⟩ := ranks_all_lemma D.R
  have e : 6 ≤ D.R.r := by
    show 6 ≤ D.R.k + D.R.m - 1
    omega
  exact_mod_cast e

theorem low_parameter_gap_lower_bound (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : 1 ≤ Cl) (τ : D.what₂.Tau) (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2) :
    Cl * (D.R.r : ℝ) ^ 19 ≤ b48 D τ ⟨j.val + 1, hj⟩ - b48 D τ j := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25⟩ := hH
  have hm := two_rS_add_two D
  rw [low_parameter_gap_eq_diff D τ j hj]
  refine le_trans ?_ (a21 τ (j.val + 1) (by omega) (by omega))
  have hL := sc_one_lt_L large₂
  have hf := two_le_fR D
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have h0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_nonneg (by linarith) (by positivity)
  calc Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right h0 hf5
    _ ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
        le_mul_of_one_le_right (mul_nonneg h0 (by positivity)) hL.le

theorem numeric_setting_of_datum (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C : ℝ) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : 1 ≤ Cl) (hC : C ≤ Cl) (τ : D.what₂.Tau) (u : D.what₂.Word) (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (hz : ∀ a : Fin D.R.rS, z (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) = 0 ∧ z (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0)
    (hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z) :
    CayleySignature.RealPlaceNumericalSetting D.R.k D.R.rS z
      (fun _ => ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) (uS D u τ) (v48 D τ) (b48 D τ) ∧
    CayleySignature.GapC C D.R.k D.R.rS (b48 D τ) := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := two_rS_add_two D
  have hN6 := six_le_n D
  have hNc := nS_cast D
  have hgap := low_parameter_gap_lower_bound D large₂ C' Cl Cg cb Cu cT CT hH hCl τ
  have hN19 : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := le_mul_of_one_le_left (by positivity) hCl
  refine ⟨⟨by omega, D.R.k_even, ?_, hT, ?_, uS_hc D u τ, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    rcases hi with hi | hi
    · exact (hz ⟨i.val, hi⟩).1
    · have hil := i.isLt
      have := (hz ⟨2 * D.R.rS + D.R.k - i.val, by omega⟩).2
      have e : Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨2 * D.R.rS + D.R.k - i.val, by omega⟩ = i := by
        apply Fin.ext; simp only [Formalism.QuantumDeterminants.esI]; omega
      rwa [e] at this
  · intro _
    have hka : 0 < D.host.ka := by
      unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
      exact div_pos Real.pi_pos (by linarith [rdE_pos D])
    have h0 : (0 : ℝ) < (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).pos
    have h1 : (0 : ℝ) < (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).pos
    have : (0 : ℝ) < 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by positivity
    exact Complex.ofReal_ne_zero.mpr this.ne'
  · rw [lambda_highest_weight_eq]; exact lamSH_hc D large₂ C' Cl Cg cb Cu cT CT hH τ
  · refine ⟨fun i => ?_, fun h => ?_⟩
    · have h1 := (D.hcW u τ).u_gt_v i
      have h2 := (D.hcW u τ).v_gt_u i
      rw [D.hcW_v u τ] at h1 h2
      simp only [v48, uS]
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · have h1 := (D.hcW u τ).u_last_gt h (by omega)
      rw [D.hcW_b u τ] at h1
      simp only [b48, uS]
      have e : (Fin.cast hm ⟨0, by omega⟩ : Fin D.R.m) = ⟨0, by omega⟩ := rfl
      rw [e]
      exact_mod_cast h1
  · intro i s
    obtain ⟨a, ha⟩ := (D.hcW u τ).u_half i
    obtain ⟨c, hc⟩ := lamSH_int D τ s
    refine ⟨a - c, ?_⟩
    rw [lambda_highest_weight_eq, hc]
    simp only [uS]; rw [ha]; push_cast; ring
  · obtain ⟨s, hs⟩ := D.R.k_even
    refine ⟨2 * D.R.rS + D.R.k + 1 + 1800, ⟨D.R.rS + s + 900, by omega⟩, by simp only [CayleySignature.rk48]; omega,
      by simp only [CayleySignature.rk48]; omega, fun j hj => ?_⟩
    refine lt_of_lt_of_le ?_ (hN19.trans (hgap j hj))
    have hmle : ((2 * D.R.rS + 2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) := by
      rw [← hNc]; exact_mod_cast (by omega : 2 * D.R.rS + 2 ≤ 2 * D.R.rS + D.R.k + 1)
    have := numNV' (D.R.r : ℝ) ((2 * D.R.rS + 2 : ℕ) : ℝ) ((D.R.r : ℝ) + 1800) hN6 hmle (by positivity) rfl
    have e1 : ((CayleySignature.rk48 D.R.k D.R.rS + (2 * D.R.rS + 2) * (2 * D.R.rS + D.R.k + 1 + 1800) : ℕ) : ℝ) =
        (D.R.r : ℝ) + ((2 * D.R.rS + 2 : ℕ) : ℝ) * ((D.R.r : ℝ) + 1800) := by
      rw [← hNc]; simp only [CayleySignature.rk48]; push_cast; ring
    have e2 : ((2 * D.R.rS + D.R.k + 1 + 1800 : ℕ) : ℝ) = (D.R.r : ℝ) + 1800 := by
      rw [← hNc]; push_cast; ring
    rw [e1, e2]; exact this
  · intro j hj
    refine lt_of_lt_of_le ?_ (hgap j hj)
    have e : ((CayleySignature.rk48 D.R.k D.R.rS : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [← hNc]; rfl
    rw [e]
    have h3 : (D.R.r : ℝ) ^ 3 < (D.R.r : ℝ) ^ 19 := pow_lt_pow_right₀ (by linarith) (by norm_num)
    have hp : 0 < (D.R.r : ℝ) ^ 3 := by positivity
    calc C * (D.R.r : ℝ) ^ 3 ≤ Cl * (D.R.r : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hC hp.le
      _ < Cl * (D.R.r : ℝ) ^ 19 := mul_lt_mul_of_pos_left h3 (by linarith)

theorem LocalBesselAndTopKernel.NV_core (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C : ℝ)
    (hy : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT) (hCl : 1 ≤ Cl) (hC : C ≤ Cl) (h : CayleySignature.Conclusion2 D C)
    (τ : D.what₂.Tau) (u : D.what₂.Word) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (π : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (w : H)
    (μG μS ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
    (hσ : IsRowsDS D τ σ) (hπ : IsColsType D u τ z π)
    (hz : ∀ a : Fin D.R.rS, z (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) = 0 ∧ z (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0)
    (hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z)
    (hw : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamSH D.R (D.hc τ)) σ w)
    (hG : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) μG)
    (hS : IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z) μS) (hQ : IsQuotMeas μG μS ν) :
    ∃ W : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → Wp,
      MeasureTheory.AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧
      MeasureTheory.AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
      IsSPsiEquiv (k := D.R.k) (r := D.R.rS) z (psiS D z) π W ∧ l2SG ν W < ⊤ ∧ l2SG ν W ≠ 0 ∧
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), rconv μG (eFun μG σ w) W x = W x := by
  obtain ⟨hSet, hGap⟩ := numeric_setting_of_datum D large₂ C' Cl Cg cb Cu cT CT C hy.2.1 hCl hC τ u z hz hT
  have hc : CompleteSpace H := by
    obtain ⟨P, _, hDS⟩ := hσ
    exact hDS.1
  have hf : FiniteDimensional ℂ Wp := by
    obtain ⟨g, _, hU⟩ := hπ
    exact hU.2.1
  have hσ' : IsDSHpk D.R.k D.R.rS (CayleySignature.eps48 D.R.k D.R.rS) (CayleySignature.lam48 D.R.k D.R.rS (v48 D τ) (b48 D τ)) σ := by
    rw [lambda_highest_weight_eq, epsilon_signature_eq]; exact hσ
  have hw' : IsLowUnitH D.R.k D.R.rS (CayleySignature.eps48 D.R.k D.R.rS) (CayleySignature.lam48 D.R.k D.R.rS (v48 D τ) (b48 D τ)) σ w := by
    rw [lambda_highest_weight_eq, epsilon_signature_eq]; exact hw
  have := h D.R.k D.R.rS z _ (uS D u τ) (v48 D τ) (b48 D τ) hSet hGap H σ hσ' Wp π hπ w hw' μG μS ν hG hS hQ
  rw [psiS_eq]
  exact this

theorem LocalBesselAndTopKernel.nonvanishing_of_gap_bound (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C : ℝ)
    (hy : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT) (hCl : 1 ≤ Cl) (hC : C ≤ Cl) (h : CayleySignature.Conclusion2 D C) : LocalBesselAndTopKernel.VolumeFromTheoremThree D := by
  intro τ u H _ _ _ σ Wp _ _ _ π z w μG μS ν hσ hπ hz hT hw hG hS hQ
  exact LocalBesselAndTopKernel.NV_core D large₂ C0 C' Cl Cg cb Cu cT CT C hy hCl hC h τ u H σ Wp π z w μG μS ν hσ hπ hz hT hw hG hS hQ

section Size

open Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB MeasureTheory
open scoped ENNReal

def SizeRange (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cs Cq0 Cr cq Cq : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (bv : ℝ), NonGenericAndKTwoTheorems.CloudNodeShape D τ Cq bv →
    Cs * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS (uS D u τ) (lamD D τ) bv ∧
    ∀ q : ℕ, (D.R.m : ℝ) * q ≤ NonGenericAndKTwoTheorems.q0 D τ cq Cq → (D.R.m : ℝ) * q ≤ bv / (Cq * (D.R.r : ℝ) ^ 4) →
      l1 (lamD D τ) (lamD D τ) + (((2 * D.R.rS + 2) * q : ℕ) : ℝ) ≤
          ThB.q0 Cq0 (2 * D.R.rS + 2) (epsSH D.R) (uS D u τ) (lamD D τ) ∧
        (((2 * D.R.rS + 2) * q + 0 : ℕ) : ℝ) ≤ bv / (Cr * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 4)

theorem sizeArith {b Cβ C2 Ch C ka m : ℝ} {n : ℕ} (hb : 1 ≤ b) (hB : Real.exp 1 ≤ b ^ Cβ) (hCh : 0 ≤ Ch) (hka0 : 0 < ka)
    (hka : 1 / ka ≤ (b ^ Cβ) ^ Ch) (hm : (n : ℝ) = m) (hC : Cβ * (C2 + Ch + 1) ≤ C) :
    (b ^ Cβ) ^ (C2 * (n : ℝ)) * (1 + 1 / ka) ^ n ≤ b ^ (C * m) := by
  have hb0 : 0 ≤ b := by linarith
  have hB2 : 2 ≤ b ^ Cβ := le_trans (by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith) hB
  have hBp : 0 < b ^ Cβ := by linarith
  have hBc : 1 ≤ (b ^ Cβ) ^ Ch := Real.one_le_rpow (by linarith) hCh
  have h1 : 1 + 1 / ka ≤ (b ^ Cβ) ^ (Ch + 1) := by
    rw [Real.rpow_add hBp, Real.rpow_one]
    nlinarith
  have hpos : 0 ≤ 1 + 1 / ka := by positivity
  have h2 : (1 + 1 / ka) ^ n ≤ ((b ^ Cβ) ^ (Ch + 1)) ^ n := pow_le_pow_left₀ hpos h1 n
  have h3 : ((b ^ Cβ) ^ (Ch + 1)) ^ n = (b ^ Cβ) ^ ((Ch + 1) * (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
  calc (b ^ Cβ) ^ (C2 * (n : ℝ)) * (1 + 1 / ka) ^ n
      ≤ (b ^ Cβ) ^ (C2 * (n : ℝ)) * (b ^ Cβ) ^ ((Ch + 1) * (n : ℝ)) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hBp.le _)
    _ = b ^ (Cβ * (C2 + Ch + 1) * m) := by
        rw [← Real.rpow_add hBp, ← Real.rpow_mul hb0, hm]; congr 1; ring
    _ ≤ b ^ (C * m) := Real.rpow_le_rpow_of_exponent_le hb
        (mul_le_mul_of_nonneg_right hC (by rw [← hm]; exact Nat.cast_nonneg _))

theorem exp_one_le_b_rpow0 {D : D7} (large₂ : SizeData₂ D) {Cβ : ℝ} (hβ : 1 ≤ Cβ) : Real.exp 1 ≤ large₂.sc.b ^ Cβ := by
  have hL : 1 ≤ large₂.sc.L := (sc_one_lt_L large₂).le
  unfold Scale.b
  rw [← Real.exp_mul]
  exact Real.exp_le_exp.2 (by nlinarith)

def TFrame0 (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ w, 1 ≤ Tr D w * kaS D ^ (2 * D.R.rS)

theorem Emom_mono {k r : ℕ} (L : LocBessel k r) (Bf : L.Hs → L.Wp) (νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (w : L.Hs)
    {X Y : Mx k r → ℝ≥0∞} (h : ∀ g, X g ≤ Y g) : Emom L Bf νq w X ≤ Emom L Bf νq w Y := by
  unfold Emom
  exact mul_le_mul' le_rfl (lintegral_mono fun x => mul_le_mul' (h _) le_rfl)

theorem NonGenericAndKTwoTheorems.lemma_M_prime_hypothesis (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH Ch Cs Cs' Cβ Cq0 Cr C2 : ℝ)
    (hMom : MomNormR D large₂ C' Cl Cg cb Cu cT CT C0 0) (hS : MuSHaar D) (hStd : StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ)
    (hTF : TFrame0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hRg : SizeRange D large₂ C' Cl Cg cb Cu cT CT C0 Cs Cq0 Cr cq Cq) (h93 : OnePlaceEstimates.SubmultiplicativeLocalNorm D Ch Cs Cq0 Cr C2)
    (hβ : 1 ≤ Cβ) (hCh : 0 ≤ Ch) (hC0 : Cβ * (C2 + Ch + 1) ≤ CH) :
    NonGenericAndKTwoTheorems.adm8 D large₂ C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH := by
  intro hH τ u bv hb θ hθ W hW A hA _ q _ hq2 hq3 la hla
  have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ) := by exact_mod_cast two_rS_add_two D
  have hb1 : 1 ≤ large₂.sc.b := (sc_one_lt_b large₂).le
  have hb0 : 0 < large₂.sc.b := by linarith
  obtain ⟨hStd1, -⟩ := hStd hH τ u u
  have hka : 0 < kaS D := hStd1.2.2.2.1
  have hC : (large₂.sc.b ^ Cβ) ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / kaS D) ^ (2 * D.R.rS + 2) ≤
      large₂.sc.b ^ (CH * (D.R.m : ℝ)) :=
    sizeArith hb1 (exp_one_le_b_rpow0 large₂ hβ) hCh hka (by rw [one_div]; exact hStd1.2.2.2.2.2.1) hm hC0
  have hT : 0 < Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTzW : Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z = Tr D u := hW.2.2.2.2.1
  have hTzW' : Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z' = Tr D u := hW.2.2.2.2.2.1
  obtain ⟨Bf, P, w0, hBf, hnorm, hP, hw0, hw0ne, hid⟩ := hMom hH τ u u θ W hW (lamD D τ) (by simp [l1dist]) A hA hT hT
  obtain ⟨hbv, hShape, hrange⟩ := hRg hH τ u bv hb
  obtain ⟨hr1, hr2⟩ := hrange q hq2 hq3
  have h1k : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hka0 : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith [rdE_pos D])
  have hv : 0 < D.host.v := by unfold Formalism.BasicNotions.Host.v; linarith [rdE_pos D]
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hκ : 0 < kapN D θ := by
    unfold kapN
    exact ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hθ0)
  have e0 : (kaS D / kaS D) ^ (2 * D.R.rS) = 1 := by rw [div_self hka.ne', one_pow]
  have hLoc : LocOk D Ch Cs (toBesselK D τ u u θ W (lamD D τ) A hW hA hT hT) (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ)
      (kaS D) := by
    refine ⟨h1k, rfl, rfl, hκ, ENNReal.ofReal_ne_top, ?_, ?_, ?_⟩
    · rw [e0, mul_one, mul_one]
      show StdHyp Ch Cs D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D u τ) (uS D u τ) (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z)
        (Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z') (kaS D) (large₂.sc.b ^ Cβ)
      rw [hTzW, hTzW']
      exact hStd1
    · show 1 ≤ Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z * kaS D ^ (2 * D.R.rS)
      rw [hTzW]; exact hTF hH u
    · show 1 ≤ Formalism.QuantumDeterminants.Tz D.R.k D.R.rS W.z' * kaS D ^ (2 * D.R.rS)
      rw [hTzW']; exact hTF hH u
  have h := h93 (toBesselK D τ u u θ W (lamD D τ) A hW hA hT hT) (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ) bv Bf W.μG
    (muS W.μW W.μN) W.νS P w0 0 hLoc.to0 hbv hShape hBf hW.2.2.2.2.2.2.1 (hS τ u u θ W hW)
    hW.2.2.2.2.2.2.2.2.2.2.2.2.1 hnorm hP (Or.inl hw0) hw0ne
  have h5 := (h.2.2.2 q hr1 hr2).2 la hla
  set c : ℝ := la * large₂.sc.b ^ (CH * (D.R.m : ℝ)) with hc
  set SS : Set (Fin (D.R.rS + 1) → ℝ) := {l | ∃ a, c ≤ max (l a) (l a)⁻¹} with hSS
  have hSSm : MeasurableSet SS := by
    have : SS = ⋃ a, {l : Fin (D.R.rS + 1) → ℝ | c ≤ max (l a) (l a)⁻¹} := by
      ext l; simp [hSS]
    rw [this]
    exact MeasurableSet.iUnion fun a =>
      measurableSet_le measurable_const ((measurable_pi_apply a).max (measurable_pi_apply a).inv)
  have hF : Measurable (SS.indicator (1 : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞)) := measurable_one.indicator hSSm
  have hid' := hid _ hF
  have hL : ∫⁻ x, Set.indicator {x | ∃ a : Fin (D.R.rS + 1), c ≤
        max (lA D.R.k D.R.rS W.z (Matrix.of x) a) (lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹}
        (fun x => (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂W.νS =
      ∫⁻ x, SS.indicator (1 : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞) (fun a => lA D.R.k D.R.rS W.z (Matrix.of x) a) *
        (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS := by
    refine lintegral_congr fun x => ?_
    by_cases hx : ∃ a : Fin (D.R.rS + 1), c ≤
        max (lA D.R.k D.R.rS W.z (Matrix.of x) a) (lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹
    · have h1 : (fun a => lA D.R.k D.R.rS W.z (Matrix.of x) a) ∈ SS := hx
      have h2 : x ∈ {x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | ∃ a : Fin (D.R.rS + 1), c ≤
        max (lA D.R.k D.R.rS W.z (Matrix.of x) a) (lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹} := hx
      rw [Set.indicator_of_mem h2, Set.indicator_of_mem h1]; simp
    · have h1 : (fun a => lA D.R.k D.R.rS W.z (Matrix.of x) a) ∉ SS := hx
      have h2 : x ∉ {x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | ∃ a : Fin (D.R.rS + 1), c ≤
        max (lA D.R.k D.R.rS W.z (Matrix.of x) a) (lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹} := hx
      rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h1]; simp
  rw [hL, hid', mul_comm]
  refine mul_le_mul' (le_trans (Emom_mono _ _ _ _ fun g => ?_) (le_trans h5 (le_of_eq ?_))) le_rfl
  · by_cases hg : (fun a => lA D.R.k D.R.rS W.z g a) ∈ SS
    · obtain ⟨a, ha⟩ := hg
      have hmem : g ∈ {g | ∃ a : Fin (D.R.rS + 1),
          la * ((large₂.sc.b ^ Cβ) ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / kaS D) ^ (2 * D.R.rS + 2)) ≤
            max (lA D.R.k D.R.rS W.z g a) (lA D.R.k D.R.rS W.z g a)⁻¹} :=
        ⟨a, le_trans (mul_le_mul_of_nonneg_left hC hla.le) ha⟩
      rw [Set.indicator_of_mem (show (fun a => lA D.R.k D.R.rS W.z g a) ∈ SS from ⟨a, ha⟩)]
      have e2 := Set.indicator_of_mem hmem (1 : Mx D.R.k D.R.rS → ℝ≥0∞)
      exact le_of_eq e2.symm
    · rw [Set.indicator_of_notMem hg]; exact bot_le
  · rw [hm]

end Size

section SizeRangeProof

open Formalism.MainNotions.S.ThB

theorem gap_all_le {n : ℕ} (f : Fin n → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ (i : Fin n) (hi : i.1 + 1 < n), G ≤ f i - f ⟨i.1 + 1, hi⟩) :
    ∀ a c : Fin n, a ≠ c → G ≤ |f a - f c| := by
  have step : ∀ i j : Fin n, j.1 = i.1 + 1 → G ≤ f i - f j := by
    intro i j hij
    have hj : i.1 + 1 < n := by omega
    have e : j = ⟨i.1 + 1, hj⟩ := Fin.ext hij
    rw [e]
    exact h i hj
  have key : ∀ d : ℕ, ∀ i j : Fin n, j.1 = i.1 + d + 1 → G ≤ f i - f j := by
    intro d
    induction d with
    | zero => intro i j hij; exact step i j (by omega)
    | succ d ih =>
      intro i j hij
      have hm : i.1 + d + 1 < n := by omega
      have h1 := ih i ⟨i.1 + d + 1, hm⟩ rfl
      have h2 := step ⟨i.1 + d + 1, hm⟩ j (by show j.1 = i.1 + d + 1 + 1; omega)
      linarith
  have G0 : ∀ i j : Fin n, i.1 < j.1 → G ≤ f i - f j := fun i j hij =>
    key (j.1 - i.1 - 1) i j (by omega)
  intro a c hac
  have hv : a.1 ≠ c.1 := fun e => hac (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
  · have h1 := G0 a c hlt
    rw [abs_of_nonneg (show (0 : ℝ) ≤ f a - f c by linarith)]
    exact h1
  · have h1 := G0 c a hgt
    rw [abs_sub_comm, abs_of_nonneg (show (0 : ℝ) ≤ f c - f a by linarith)]
    exact h1

theorem lamD_v (D : D7) (τ : D.what₂.Tau) (s : Fin (2 * D.R.rS + D.R.k + 1)) (h : s.val < D.R.k - 1) :
    lamD D τ s = ((D.hc τ).v ⟨s.val, h⟩ : ℝ) := by
  simp [lamD, lamSH, lamS, h]

theorem lamD_b (D : D7) (τ : D.what₂.Tau) (s : Fin (2 * D.R.rS + D.R.k + 1)) (h : ¬ s.val < D.R.k - 1)
    (h' : s.val - (D.R.k - 1) < D.R.m) : lamD D τ s = -((D.hc τ).b ⟨s.val - (D.R.k - 1), h'⟩ : ℝ) := by
  simp [lamD, lamSH, lamS, h, h']

theorem isCloud_iff (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (u : D.what₂.Word) (s : Fin (2 * D.R.rS + D.R.k + 1)) :
    IsCloud (uS D u τ) (lamD D τ) s ↔ s.val < D.R.k - 1 := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := two_rS_add_two D
  constructor
  · rintro ⟨_, i, hi⟩
    by_contra hs
    have hanti := (lamSH_hc D large₂ C' Cl Cg cb Cu cT CT hH τ).1.antitone
    have hle : (⟨D.R.k - 1, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) ≤ s := by
      show D.R.k - 1 ≤ s.val
      omega
    have h1 : lamD D τ s ≤ lamD D τ ⟨D.R.k - 1, by omega⟩ := hanti hle
    have h2 : lamD D τ ⟨D.R.k - 1, by omega⟩ = -((D.hc τ).b ⟨0, by omega⟩ : ℝ) := by
      rw [lamD_b D τ _ (by simp) (by simp; omega)]
      simp
    have h3 := (D.hcW u τ).u_last_gt (by omega) (by omega)
    rw [D.hcW_b u τ] at h3
    have h3' : -((D.hc τ).b ⟨0, by omega⟩ : ℝ) < uS D u τ ⟨D.R.k - 1, by omega⟩ := by
      simp only [uS]; exact_mod_cast h3
    have h4 : uS D u τ ⟨D.R.k - 1, by omega⟩ ≤ uS D u τ i :=
      (uS_dec D u τ).antitone (by show i.val ≤ D.R.k - 1; have := i.isLt; omega)
    linarith
  · intro hs
    have h1 := (D.hcW u τ).u_gt_v ⟨s.val, hs⟩
    have h2 := (D.hcW u τ).v_gt_u ⟨s.val, hs⟩
    rw [D.hcW_v u τ] at h1 h2
    rw [IsCloud, lamD_v D τ s hs]
    exact ⟨⟨⟨s.val, by omega⟩, by simp only [uS]; exact_mod_cast h1⟩,
      ⟨⟨s.val + 1, by omega⟩, by simp only [uS]; exact_mod_cast h2⟩⟩

theorem cloudGap_ge (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (u : D.what₂.Word) : 4 * (D.s.Del : ℝ) ≤ cloudGap (uS D u τ) (lamD D τ) := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hDel : (0 : ℝ) < (D.s.Del : ℝ) := by exact_mod_cast D.s.Del_pos
  have hv := gap_all_le (fun i : Fin (D.R.k - 1) => ((D.hc τ).v i : ℝ)) (4 * (D.s.Del : ℝ)) (by linarith)
    (fun i hi => by
      have := D.s.cloud_gap u τ i.1 hi
      rw [D.hcW_v u τ] at this
      have e : ((D.hc τ).v i : ℝ) - ((D.hc τ).v ⟨i.1 + 1, hi⟩ : ℝ) = 4 * (D.s.Del : ℝ) := by exact_mod_cast this
      exact e.ge)
  unfold cloudGap
  refine le_csInf ?_ ?_
  · refine ⟨_, ⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], ?_, ?_, rfl⟩
    · exact (isCloud_iff D large₂ C' Cl Cg cb Cu cT CT hH τ u _).mpr (by show 0 < D.R.k - 1; omega)
    · exact (isCloud_iff D large₂ C' Cl Cg cb Cu cT CT hH τ u _).mpr (by show 1 < D.R.k - 1; omega)
  · rintro x ⟨a, b, hab, ha, hb, rfl⟩
    have ha' := (isCloud_iff D large₂ C' Cl Cg cb Cu cT CT hH τ u a).mp ha
    have hb' := (isCloud_iff D large₂ C' Cl Cg cb Cu cT CT hH τ u b).mp hb
    rw [lamD_v D τ a ha', lamD_v D τ b hb']
    exact hv ⟨a.val, ha'⟩ ⟨b.val, hb'⟩ (by
      intro hc
      exact hab (Fin.ext (by simpa using congrArg Fin.val hc)))

theorem sizeRange_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cs Cq0 Cr : ℝ) (h0 : 0 < Cq0) (hr : 0 < Cr) :
    SizeRange D large₂ C' Cl Cg cb Cu cT CT C0 Cs Cq0 Cr (1 / max (max Cs Cq0) (max Cr 1)) (max (max Cs Cq0) (max Cr 1)) := by
  set Cq : ℝ := max (max Cs Cq0) (max Cr 1) with hCq
  have hCs : Cs ≤ Cq := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC0 : Cq0 ≤ Cq := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCr : Cr ≤ Cq := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1 : 1 ≤ Cq := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCqp : 0 < Cq := by linarith
  intro hH τ u bv hb
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := two_rS_add_two D
  have hNc := nS_cast D
  have hN6 := six_le_n D
  have hmR : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ) := by exact_mod_cast hm
  have hbv0 : 0 ≤ bv := le_trans (mul_nonneg hCqp.le (by positivity)) hb1
  refine ⟨?_, ?_, ?_⟩
  · rw [hNc]; exact le_trans (mul_le_mul_of_nonneg_right hCs (by positivity)) hb1
  · intro s
    have hs := s.isLt
    by_cases hc : s.val < D.R.k - 1
    · have hcl := (isCloud_iff D large₂ C' Cl Cg cb Cu cT CT hH.1 τ u s).mpr hc
      refine ⟨fun _ => ?_, fun hn => absurd hcl hn⟩
      have := hb2 (s.val + 1) (by omega) (by omega)
      have e : vOne D τ (s.val + 1) = lamD D τ s := by
        rw [lamD_v D τ s hc]
        have h1 : 1 ≤ s.val + 1 ∧ s.val + 1 ≤ D.R.k - 1 := ⟨by omega, by omega⟩
        simp [vOne, h1]
      rwa [e] at this
    · have hcl : ¬ IsCloud (uS D u τ) (lamD D τ) s := fun h =>
        hc ((isCloud_iff D large₂ C' Cl Cg cb Cu cT CT hH.1 τ u s).mp h)
      refine ⟨fun h => absurd h hcl, fun _ => ?_⟩
      have hj : s.val - (D.R.k - 1) < D.R.m := by omega
      have := hb3 (s.val - (D.R.k - 1) + 1) (by omega) (by omega)
      have e : bOne D τ (s.val - (D.R.k - 1) + 1) = -lamD D τ s := by
        rw [lamD_b D τ s hc hj]
        have h1 : 1 ≤ s.val - (D.R.k - 1) + 1 ∧ s.val - (D.R.k - 1) + 1 ≤ D.R.m := ⟨by omega, by omega⟩
        simp [bOne, h1]
      rw [e] at this
      constructor <;> linarith [this.1, this.2]
  · intro q hq2 hq3
    have hcast : (((2 * D.R.rS + 2) * q : ℕ) : ℝ) = (D.R.m : ℝ) * q := by push_cast; rw [← hmR]; push_cast; ring
    constructor
    · have hl1 : l1 (lamD D τ) (lamD D τ) = 0 := by simp [l1]
      rw [hl1, zero_add, hcast]
      refine le_trans hq2 ?_
      have hh : 0 ≤ hNC (epsSH D.R) (lamD D τ) := by
        unfold hNC
        exact Real.sInf_nonneg (by rintro x ⟨a, b, _, rfl⟩; exact abs_nonneg _)
      have hmpos : (0 : ℝ) < (D.R.m : ℝ) := by exact_mod_cast (by omega : 0 < D.R.m)
      have hsq : (D.R.m : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (D.R.m : ℝ) := by
        rw [Real.rpow_neg hmpos.le, Real.sqrt_eq_rpow]
        exact (one_div _).symm
      have hsp : 0 < Real.sqrt (D.R.m : ℝ) := Real.sqrt_pos.mpr hmpos
      have hA : 1 / Cq * NonGenericAndKTwoTheorems.hNC D τ * (D.R.m : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          hNC (epsSH D.R) (lamD D τ) / (Cq0 * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)) := by
        rw [hmR, hsq]
        have e1 : NonGenericAndKTwoTheorems.hNC D τ = hNC (epsSH D.R) (lamD D τ) := rfl
        rw [e1]
        have e2 : 1 / Cq * hNC (epsSH D.R) (lamD D τ) * (1 / Real.sqrt (D.R.m : ℝ)) =
            hNC (epsSH D.R) (lamD D τ) / (Cq * Real.sqrt (D.R.m : ℝ)) := by field_simp
        rw [e2]
        exact div_le_div_of_nonneg_left hh (by positivity) (mul_le_mul_of_nonneg_right hC0 hsp.le)
      have hB := cloudGap_ge D large₂ C' Cl Cg cb Cu cT CT hH.1 τ u
      have hDel : (0 : ℝ) < (D.s.Del : ℝ) := by exact_mod_cast D.s.Del_pos
      have hmin : min (1 / Cq * NonGenericAndKTwoTheorems.hNC D τ * (D.R.m : ℝ) ^ (-(1 / 2 : ℝ))) (4 * (D.s.Del : ℝ)) ≤
          min (hNC (epsSH D.R) (lamD D τ) / (Cq0 * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)))
            (cloudGap (uS D u τ) (lamD D τ)) := min_le_min hA hB
      have hM0 : 0 ≤ min (hNC (epsSH D.R) (lamD D τ) / (Cq0 * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)))
            (cloudGap (uS D u τ) (lamD D τ)) :=
        le_min (div_nonneg hh (mul_nonneg h0.le (Real.sqrt_nonneg _))) (by linarith)
      unfold NonGenericAndKTwoTheorems.q0 ThB.q0
      calc _ ≤ min (hNC (epsSH D.R) (lamD D τ) / (Cq0 * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)))
            (cloudGap (uS D u τ) (lamD D τ)) / Cq := div_le_div_of_nonneg_right hmin hCqp.le
        _ ≤ _ := div_le_div_of_nonneg_left hM0 h0 hC0
    · have e : (((2 * D.R.rS + 2) * q + 0 : ℕ) : ℝ) = (D.R.m : ℝ) * q := by rw [Nat.add_zero]; exact hcast
      rw [e, hNc]
      refine le_trans hq3 ?_
      exact div_le_div_of_nonneg_left hbv0 (by positivity) (mul_le_mul_of_nonneg_right hCr (by positivity))

end SizeRangeProof

section SizeFam

open Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem NonGenericAndKTwoTheorems.family_moment_bounds_of_source (Ch Cβ Cs Cq0 Cr C2 : ℝ) (hCh : 0 ≤ Ch) (hβ : 1 ≤ Cβ) (hq0 : 0 < Cq0) (hr : 0 < Cr)
    (h93 : OnePlaceEstimates.FamilySubmultiplicativeNorm Fm Ch Cs Cq0 Cr C2) (bMom : PX.Mom Fm) (bHaar : PX.SHaar Fm)
    (bStd : ∀ Cg cb Cu cT CT C0 : ℝ, PX.StdHypS Fm Cg cb Cu cT CT C0 Ch Cβ)
    (bTF : ∀ Cg cb Cu cT CT C0 : ℝ, PX.TFrame Fm Cg cb Cu cT CT C0) : NonGenericAndKTwoTheorems.admF8 Fm := by
  intro Cg cb Cu cT CT C0 Cθ
  have hCq : 0 < max (max Cs Cq0) (max Cr 1) :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  exact ⟨1 / max (max Cs Cq0) (max Cr 1), max (max Cs Cq0) (max Cr 1), Cβ * (C2 + Ch + 1), by positivity, hCq, fun C1 =>
    OwnEv.mono (fun C' Cl x i H =>
      NonGenericAndKTwoTheorems.lemma_M_prime_hypothesis _ _ _ _ _ _ _ _ _ _ Cθ C1 _ _ _ Ch Cs 0 Cβ Cq0 Cr C2 H.2 (bHaar x i) H.1.1 H.1.2
        (sizeRange_of _ _ _ _ _ _ _ _ _ _ Cs Cq0 Cr hq0 hr) (h93 x i) hβ hCh le_rfl)
      (((bStd Cg cb Cu cT CT C0 Cs 0).and (bTF Cg cb Cu cT CT C0)).and (bMom Cg cb Cu cT CT C0 0))⟩

end SizeFam

theorem UniformConstantsAndStatements.sizes_bound_of_log_estimates (D : D7) (C : ℝ) (h : NonGenericAndKTwoTheorems.Conclusion1 D C) : UniformConstantsAndStatements.adm5 D C := by
  first
    | exact h
    | exact fun _ => h

theorem UniformConstantsAndStatements.restriction_dimension_of_division (D : D7) (Ch Cg Cb : ℝ) (h : OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) : UniformConstantsAndStatements.adm6 D Ch Cg Cb := by
  first
    | exact h
    | exact fun _ => h

theorem UniformConstantsAndStatements.crystalline_lift_of_theorem_c (D : D7) (large₂ : SizeData₂ D) (s : UniformConstantsAndStatements.LargenessConstants) (C1 A c : ℝ)
    (hCl : 2 < s.Cl) (hC' : 1 ≤ s.C') (hA : 1 ≤ A) (hb : UniformConstantsAndStatements.Hyp D large₂ s → Sizes3b D A)
    (h : ∀ u u', AuxiliaryNormPrimes.aux₃ D large₂ u u' s.C' s.Cl s.Cg s.cb s.Cu s.cT s.CT s.C0 A c) :
    UniformConstantsAndStatements.adm9 D large₂ s C1 c :=
  fun hy _ u u' S hS =>
    h u u' (count_hypotheses_of_sizes D large₂ s.C' s.Cl s.Cg s.cb s.Cu s.cT s.CT s.C0 A hy.1 hy.2.1 hy.2.2 hCl hC' hA (hb hy) u u') S hS

theorem FrobeniusProjectedBounds.sizes_bound_of_log_estimates (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 c C : ℝ)
    (h : UniformConstantsAndStatements.Conclusion1 D large₂ ⟨C0, C', Cl, Cg, cb, Cu, cT, CT⟩ c C) : FrobeniusProjectedBounds.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 c C :=
  fun hy u u' => h ⟨hy.2.1, hy.1, hy.2.2⟩ u u'

theorem AdmissibleBoundsFromSource.lemma_M_prime_hypothesis (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C : ℝ)
    (h : UniformConstantsAndStatements.Conclusion2 D large₂ ⟨C0, C', Cl, Cg, cb, Cu, cT, CT⟩ C) : AdmissibleBoundsFromSource.adm8 D large₂ C0 C' Cl Cg cb Cu cT CT C := by
  first
    | exact h
    | exact fun _ => h

theorem FrobeniusProjectedBounds.restriction_dimension_of_division (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C : ℝ)
    (h : UniformConstantsAndStatements.Conclusion2 D large₂ ⟨C0, C', Cl, Cg, cb, Cu, cT, CT⟩ C) : FrobeniusProjectedBounds.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 C :=
  fun hy u => h ⟨hy.2.1, hy.1, hy.2.2⟩ u

theorem NonGenericAndKTwoTheorems.integrality_of_commutation (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hId : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word, IdCellDiag D.s u)
    (h : FrobeniusProjectedBounds.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0) : NonGenericAndKTwoTheorems.adm3 D large₂ X C' Cl Cg cb Cu cT CT C0 :=
  fun hy => ⟨fun u t hf hr => (h hy u).2.2.2.1 t hf hr, hId hy⟩

theorem LatticeIndexAndWeightTheory.restriction_dimension_of_division (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (h : FrobeniusProjectedBounds.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0) : LatticeIndexAndWeightTheory.adm6 D large₂ X C' Cl Cg cb Cu cT CT C0 :=
  fun hy u t hf hr => (h hy u).2.2.2.1 t hf hr

theorem count_hypotheses_diagonal_words (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A : ℝ)
    (hD : StandingNumericalData D C0) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h0 : 1 ≤ C0) (hCl : 2 < Cl) (hC' : 1 ≤ C')
    (hA : 1 ≤ A) (u : D.what₂.Word) : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 A := by
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hTT : ((D.mem u).A.T : ℝ) / ((D.mem u).A.T : ℝ) ≤ A := by rw [div_self hT.ne']; exact hA
  have hv : ∀ τ, vand (uS D u τ) ≤ A ^ D.R.k * vand (uS D u τ) := fun τ =>
    le_mul_of_one_le_left (vand_uS_pos D u τ).le (one_le_pow₀ hA)
  exact ⟨⟨hH, hD, h0⟩, Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hD hH hCl u u, hTT, hTT,
    klogk_of D large₂ C' Cl Cg cb Cu cT CT hH hC', (logf_of D large₂ C' Cl Cg cb Cu cT CT A hH hA).1,
    (logf_of D large₂ C' Cl Cg cb Cu cT CT A hH hA).2, fun τ => ⟨hv τ, hv τ⟩⟩

theorem NonGenericAndKTwoTheorems.diagonal_count_bound_of_source (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ)
    (hCl : 2 < Cl) (hC' : 1 ≤ C') (hA : 1 ≤ A)
    (h : VanishingOnXAndXPlusMass.Conclusion1 D large₂ D.u₀ D.u₀ C' Cl Cg cb Cu cT CT C0 A C c) : NonGenericAndKTwoTheorems.RankTwoMassHypothesis D large₂ C' Cl Cg cb Cu cT CT C0 C :=
  fun hy => (h (count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 A hy.1.2.1 hy.1.1 hy.1.2.2 hCl hC' hA D.u₀)).1

theorem LatticeIndexAndWeightTheory.diagonal_count_bound_of_source (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ)
    (hCl : 2 < Cl) (hC' : 1 ≤ C') (hA : 1 ≤ A)
    (h : VanishingOnXAndXPlusMass.Conclusion1 D large₂ D.u₀ D.u₀ C' Cl Cg cb Cu cT CT C0 A C c) : LatticeIndexAndWeightTheory.RankTwoMassHypothesis D large₂ C' Cl Cg cb Cu cT CT C0 C :=
  fun hy => (h (count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 A hy.1.2.1 hy.1.1 hy.1.2.2 hCl hC' hA D.u₀)).1

theorem CayleySignature.capelli_identities_admissible (D : D7) : CayleySignature.adm8 D :=
  ⟨Formalism.QuantumDeterminants.capelliHW, Formalism.QuantumDeterminants.capCentral, Formalism.QuantumDeterminants.qMinorLeft, Formalism.QuantumDeterminants.capLeft, Formalism.QuantumDeterminants.capHW,
    Formalism.QuantumDeterminants.capComatrix⟩

theorem CayleySignature.fock_pair_admissible (D : D7) : CayleySignature.adm9 D :=
  ⟨Formalism.REAL.cCR, Formalism.REAL.fockPairGl, Formalism.REAL.fockAdj, Formalism.REAL.fockCas⟩

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem CayleySignature.theta_norm_family_of_linked (h : PlaceDegreeData.FamilyLowestKTypeFormula Fm) : CayleySignature.admF1 Fm := fun x i => CayleySignature.first_hypothesis_of_lifting _ (h x i)

theorem CayleySignature.theta_condition_family_of_linked (h : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm) : CayleySignature.admF2 Fm := fun x i => CayleySignature.second_hypothesis_of_lifting _ (h x i)

theorem FrobeniusProjectedBounds.stabiliser_family_of_definite (Cg cb Cu cT CT C0 : ℝ) (h1 : 1 ≤ sC' Fm) (h : NonGenericAndKTwoTheorems.Conclusion2Family Fm) :
    FrobeniusProjectedBounds.admF3 Fm Cg cb Cu cT CT C0 := by
  obtain ⟨x0, H⟩ := h Cg cb Cu cT CT C0
  exact ⟨x0, fun x hx i => FrobeniusProjectedBounds.integrality_of_commutation _ _ _ _ _ _ _ _ _ _ h1 (H x hx i)⟩

theorem sizes3bF (C0 Cg cb Cu cT CT C1 C2 A : ℝ) (h0 : 0 ≤ C1) (h1 : C1 ≤ A) (h2 : C2 ≤ A)
    (hb : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT C1) (hc : LocalBesselAndTopKernel.FamilyLowestKType Fm C0 Cg cb Cu cT CT C2) :
    OwnEv Fm fun C' Cl x i =>
      LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → Sizes3b (Fm.D x i) A := by
  obtain ⟨x1, H1⟩ := hb
  obtain ⟨x2, H2⟩ := hc
  exact ⟨max x1 x2, fun x hx i hy => sizes_of_vandermonde_bounds _ C1 C2 A h0 h1 h2
    (H1 x (le_trans (le_max_left _ _) hx) i hy) (H2 x (le_trans (le_max_right _ _) hx) i hy)⟩

theorem FrobeniusProjectedBounds.injectivity_family_of_theorem (Cg cb Cu cT CT C0 C1 C2 A c : ℝ) (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm) (hA : 1 ≤ A)
    (h0 : 0 ≤ C1) (h1 : C1 ≤ A) (h2 : C2 ≤ A)
    (hb : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT C1) (hc : LocalBesselAndTopKernel.FamilyLowestKType Fm C0 Cg cb Cu cT CT C2)
    (h : AuxiliaryNormPrimes.OrbitValuationBound Fm c) : FrobeniusProjectedBounds.admF4 Fm Cg cb Cu cT CT C0 c := by
  obtain ⟨x0, H⟩ := OwnEv.and (sizes3bF Fm C0 Cg cb Cu cT CT C1 C2 A h0 h1 h2 hb hc) (h.2 Cg cb Cu cT CT C0 A)
  exact ⟨x0, fun x hx i => FrobeniusProjectedBounds.fourth_hypothesis_of_lifting _ _ _ _ _ _ _ _ _ _ A c hCl hC' hA
    (fun hy => (H x hx i).1 ⟨hy.2.1, hy.1, hy.2.2⟩) (H x hx i).2⟩

theorem FrobeniusProjectedBounds.family_ev_bound_of_source (g : UniformConstantsAndStatements.Given) (c C : ℝ) (h : UniformConstantsAndStatements.ConclusionF1 Fm g c C) :
    FrobeniusProjectedBounds.admF5 Fm g.Cg g.cb g.Cu g.cT g.CT g.C0 c C :=
  OwnEv.mono (fun _ _ _ _ hh => FrobeniusProjectedBounds.sizes_bound_of_log_estimates _ _ _ _ _ _ _ _ _ _ _ _ hh) h

theorem FrobeniusProjectedBounds.norm_bound_family_of_theorem (g : UniformConstantsAndStatements.Given) (C : ℝ) (h : UniformConstantsAndStatements.ConclusionF2 Fm g C) :
    FrobeniusProjectedBounds.admF6 Fm g.Cg g.cb g.Cu g.cT g.CT g.C0 C :=
  OwnEv.mono (fun _ _ _ _ hh => FrobeniusProjectedBounds.restriction_dimension_of_division _ _ _ _ _ _ _ _ _ _ _ hh) h

theorem UniformConstantsAndStatements.family_ev_bound_of_source (C : ℝ) (h : NonGenericAndKTwoTheorems.Conclusion1Family Fm C) : UniformConstantsAndStatements.admF5 Fm C := by
  first
    | exact h
    | exact fun _ => h

theorem UniformConstantsAndStatements.family_count_bound_of_source (g : UniformConstantsAndStatements.Given) (C1 C2 A c : ℝ) (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm) (hA : 1 ≤ A)
    (h0 : 0 ≤ C1) (h1 : C1 ≤ A) (h2 : C2 ≤ A)
    (hb : LocalBesselAndTopKernel.TheoremThreePassage Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C1) (hc : LocalBesselAndTopKernel.FamilyLowestKType Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C2)
    (h : AuxiliaryNormPrimes.OrbitValuationBound Fm c) : UniformConstantsAndStatements.admF9 Fm g c := by
  obtain ⟨x0, H⟩ := OwnEv.and (sizes3bF Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C1 C2 A h0 h1 h2 hb hc)
    (h.2 g.Cg g.cb g.Cu g.cT g.CT g.C0 A)
  exact ⟨x0, fun x hx i => UniformConstantsAndStatements.crystalline_lift_of_theorem_c _ _ (g.wth (sC' Fm) (sCl Fm)) _ A c hCl hC' hA
    (fun hy => (H x hx i).1 hy) (H x hx i).2⟩

theorem LatticeIndexAndWeightTheory.norm_bound_family_of_theorem (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
    (h : ∀ Cg cb Cu cT CT C0 : ℝ, FrobeniusProjectedBounds.ConclusionF1 Fm At Cg cb Cu cT CT C0) : LatticeIndexAndWeightTheory.admF6 Fm At :=
  fun Cg cb Cu cT CT C0 =>
    OwnEv.mono (fun _ _ _ _ hh hx => LatticeIndexAndWeightTheory.restriction_dimension_of_division _ _ _ _ _ _ _ _ _ _ _ (hh hx)) (h Cg cb Cu cT CT C0)

theorem AdmissibleBoundsFromSource.stabiliser_family_of_definite (gc : AdmissibleBoundsFromSource.GivC) (h : NonGenericAndKTwoTheorems.Conclusion3Family Fm) : AdmissibleBoundsFromSource.admF3 Fm gc :=
  OwnEv.mono (fun _ _ _ _ hh => AdmissibleBoundsFromSource.integrality_of_commutation _ _ _ _ _ _ _ _ _ _ hh) (h gc.Cg gc.cb gc.Cu gc.cT gc.CT gc.C0)

theorem AdmissibleBoundsFromSource.family_ev_bound_of_source (gc : AdmissibleBoundsFromSource.GivC) (h : NonGenericAndKTwoTheorems.Conclusion2Family Fm) : AdmissibleBoundsFromSource.admF5 Fm gc :=
  OwnEv.mono (fun _ _ _ _ hh => AdmissibleBoundsFromSource.sizes_bound_of_log_estimates _ _ _ _ _ _ _ _ _ _ hh) (h gc.Cg gc.cb gc.Cu gc.cT gc.CT gc.C0)

theorem AdmissibleBoundsFromSource.norm_bound_family_of_theorem (gc : AdmissibleBoundsFromSource.GivC) (A c : ℝ) (h : AuxiliaryNormPrimes.OrbitValuationBound Fm c) : AdmissibleBoundsFromSource.admF6 Fm gc A c :=
  OwnEv.mono (fun _ _ _ _ hh => AdmissibleBoundsFromSource.restriction_dimension_of_division _ _ _ _ _ _ _ _ _ _ _ _ hh) (h.2 gc.Cg gc.cb gc.Cu gc.cT gc.CT gc.C0 A)

theorem AdmissibleBoundsFromSource.family_ev_bound_seven_of_source (g : UniformConstantsAndStatements.Given) (c C : ℝ) (h : UniformConstantsAndStatements.ConclusionF1 Fm g c C) :
    AdmissibleBoundsFromSource.admF7 Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩ c C := by
  first
    | exact h
    | exact fun _ => h

theorem AdmissibleBoundsFromSource.family_moment_bounds_of_source (g : UniformConstantsAndStatements.Given) (C : ℝ) (h : UniformConstantsAndStatements.ConclusionF2 Fm g C) :
    AdmissibleBoundsFromSource.admF8 Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩ C := by
  first
    | exact h
    | exact fun _ => h

theorem AdmissibleBoundsFromSource.family_count_bound_of_source (gc : AdmissibleBoundsFromSource.GivC) (CA CA' Ce : ℝ)
    (h : LocalBesselAndTopKernel.ConclusionF1 Fm gc.C0 gc.Cg gc.cb gc.Cu gc.cT gc.CT CA CA' Ce) : AdmissibleBoundsFromSource.admF9 Fm gc CA CA' Ce := by
  obtain ⟨x0, H⟩ := h
  exact ⟨x0, fun x hx i hy => AdmissibleBoundsFromSource.crystalline_lift_of_theorem_c _ _ _ _ _ _ _ _ _ _ CA CA' Ce (H x hx i hy) hy⟩

theorem AdmissibleBoundsFromSource.family_volume_lower_of_source (gc : AdmissibleBoundsFromSource.GivC) (ep0 CV : ℝ)
    (h : LocalBesselAndTopKernel.FamilyTopBound Fm gc.C0 gc.Cg gc.cb gc.Cu gc.cT gc.CT ep0 CV) : AdmissibleBoundsFromSource.FamilyVandermondeLowerBound Fm gc ep0 := by
  obtain ⟨x0, H⟩ := h
  exact ⟨x0, fun x hx i hy => AdmissibleBoundsFromSource.volume_bounds_of_source _ _ _ _ _ _ _ _ _ _ ep0 CV (H x hx i hy) hy⟩

theorem AdmissibleBoundsFromSource.family_volume_upper_of_source (gc : AdmissibleBoundsFromSource.GivC) (ep0 CV : ℝ)
    (h : LocalBesselAndTopKernel.FamilyTopBound Fm gc.C0 gc.Cg gc.cb gc.Cu gc.cT gc.CT ep0 CV) : AdmissibleBoundsFromSource.FamilyVandermondeUpperBound Fm gc CV := by
  obtain ⟨x0, H⟩ := h
  exact ⟨x0, fun x hx i hy => AdmissibleBoundsFromSource.volume_upper_bound_of_source _ _ _ _ _ _ _ _ _ _ ep0 CV (H x hx i hy) hy⟩

theorem AdmissibleBoundsFromSource.family_size_bounds_of_source (gc : AdmissibleBoundsFromSource.GivC) (C1 C2 c5 CA : ℝ)
    (ha : LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm gc.C0 gc.Cg gc.cb gc.Cu gc.cT gc.CT)
    (hb : LocalBesselAndTopKernel.TheoremThreePassage Fm gc.C0 gc.Cg gc.cb gc.Cu gc.cT gc.CT C1)
    (hc : LocalBesselAndTopKernel.FamilyLowestKType Fm gc.C0 gc.Cg gc.cb gc.Cu gc.cT gc.CT C2)
    (hf : LocalBesselAndTopKernel.FamilyLocalBesselBoundWithCharacter Fm gc.C0 gc.Cg gc.cb gc.Cu gc.cT gc.CT c5 CA) : AdmissibleBoundsFromSource.FamilyThirteenthHypothesis Fm gc C1 C2 c5 CA := by
  obtain ⟨x1, H1⟩ := ha
  obtain ⟨x2, H2⟩ := hb
  obtain ⟨x3, H3⟩ := hc
  obtain ⟨x4, H4⟩ := hf
  refine ⟨max (max x1 x2) (max x3 x4), fun x hx i hy => ⟨H1 x ?_ i hy, H2 x ?_ i hy, H3 x ?_ i hy, H4 x ?_ i hy⟩⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx

end Family

section Assembly

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem under_a {P Q : ∀ x (_ : Fm.Ix x), Prop} (h : PX.Under Fm P) (C0 Cg cb Cu cT CT : ℝ)
    (f : ∀ x i, P x i → Q x i) :
    OwnEv Fm fun C' Cl x i => PX.H0 (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → Q x i :=
  OwnEv.mono (fun _ _ x i hh hy => f x i (hh hy)) (h C0 Cg cb Cu cT CT)

theorem under_b {P Q : ∀ x (_ : Fm.Ix x), Prop} (h : PX.Under Fm P) (C0 Cg cb Cu cT CT : ℝ)
    (f : ∀ x i, P x i → Q x i) :
    OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → Q x i :=
  OwnEv.mono (fun _ _ x i hh hy => f x i (hh ⟨hy.2.1, hy.1, hy.2.2⟩)) (h C0 Cg cb Cu cT CT)

theorem under_bG {P Q : ∀ x, Fm.x1 < x → ∀ _ : Fm.Ix x, Prop} (h : PX.UnderG Fm P) (C0 Cg cb Cu cT CT : ℝ)
    (f : ∀ x hx i, P x hx i → Q x hx i) :
    OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → Q x hx i :=
  OwnEv.mono (fun _ _ x i hh hx hy => f x hx i (hh hx ⟨hy.2.1, hy.1, hy.2.2⟩)) (h C0 Cg cb Cu cT CT)

def Sizes3bF : Prop := ∀ C0 Cg cb Cu cT CT : ℝ, ∃ A : ℝ, 1 ≤ A ∧
  OwnEv Fm fun C' Cl x i => PX.H0 (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → Sizes3b (Fm.D x i) A

theorem AdmissibleBoundsFromSource.family_first_package_of_source (g : UniformConstantsAndStatements.Given) (ca : AdmissibleBoundsFromSource.AdmC)
    (pExp : PX.ExpF Fm) (pId : PX.IdCellF Fm) (p2a : PX.TwoAF Fm) (familyVolumeLowerBound : PX.FamilyVanishingCondition Fm) (pIdG : PX.FamilyIdentityCondition Fm)
    (familyStandingLowerBound : PX.FamilyFirstSumAtLeastOne Fm) (pAbs : PX.PairAbsF Fm)
    (lWeyl : AdmissibleBoundsFromSource.FamilyWeylDimension Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩) (iMass : AdmissibleBoundsFromSource.FamilyTwelfthHypothesis)
    (h29b : NonGenericAndKTwoTheorems.Conclusion2Family Fm) (h29c : NonGenericAndKTwoTheorems.Conclusion3Family Fm) (h28 : AuxiliaryNormPrimes.OrbitValuationBound Fm ca.cL)
    (hN1 : UniformConstantsAndStatements.ConclusionF1 Fm g ca.cN ca.CN) (hN2 : UniformConstantsAndStatements.ConclusionF2 Fm g ca.CE)
    (h27 : LocalBesselAndTopKernel.ConclusionF1 Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT ca.CA ca.CA' ca.Ce)
    (h27a : LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT) (h27b : LocalBesselAndTopKernel.TheoremThreePassage Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT ca.C1)
    (h27c : LocalBesselAndTopKernel.FamilyLowestKType Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT ca.C2)
    (h27f : LocalBesselAndTopKernel.FamilyLocalBesselBoundWithCharacter Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT ca.c5 ca.CA)
    (h27g : LocalBesselAndTopKernel.FamilyTopBound Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT ca.ep0 ca.CV) :
    AdmissibleBoundsFromSource.FirstFiltrationHypotheses Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩ ca :=
  ⟨under_a Fm pExp _ _ _ _ _ _ (fun _ _ h => h), under_a Fm pId _ _ _ _ _ _ (fun _ _ h => h),
    AdmissibleBoundsFromSource.stabiliser_family_of_definite Fm _ h29c,
    under_a Fm p2a _ _ _ _ _ _ (fun _ _ h u u' Φ hS _ hs => h u u' Φ hS hs),
    AdmissibleBoundsFromSource.family_ev_bound_of_source Fm _ h29b, AdmissibleBoundsFromSource.norm_bound_family_of_theorem Fm _ _ _ h28, AdmissibleBoundsFromSource.family_ev_bound_seven_of_source Fm g _ _ hN1, AdmissibleBoundsFromSource.family_moment_bounds_of_source Fm g _ hN2,
    AdmissibleBoundsFromSource.family_count_bound_of_source Fm _ _ _ _ h27,
    ⟨lWeyl, AdmissibleBoundsFromSource.family_volume_lower_of_source Fm _ _ _ h27g, AdmissibleBoundsFromSource.family_volume_upper_of_source Fm _ _ _ h27g⟩, iMass,
    AdmissibleBoundsFromSource.family_size_bounds_of_source Fm _ _ _ _ _ h27a h27b h27c h27f,
    OwnEv.mono (fun _ _ _ _ hh hy u u' => ⟨hh.1 hy u u', hh.2.1 hy u u', hh.2.2 hy u u'⟩)
      (OwnEv.and (familyVolumeLowerBound g.C0 g.Cg g.cb g.Cu g.cT g.CT)
        (OwnEv.and (pIdG g.C0 g.Cg g.cb g.Cu g.cT g.CT) (familyStandingLowerBound g.C0 g.Cg g.cb g.Cu g.cT g.CT))),
    under_a Fm pAbs _ _ _ _ _ _ (fun _ _ h => h)⟩

theorem FrobeniusProjectedBounds.AdmF_of (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (g : UniformConstantsAndStatements.Given) (C1 C2 A cL cN CN CE c7 : ℝ)
    (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm) (hA : 1 ≤ A) (h0 : 0 ≤ C1) (h1 : C1 ≤ A) (h2 : C2 ≤ A)
    (pExp : PX.ExpF Fm) (p2a : PX.TwoAF Fm) (familyVolumeLowerBound : PX.FamilyVanishingCondition Fm) (pId : PX.IdCellF Fm) (pG : PX.GDrF Fm At)
    (h29 : NonGenericAndKTwoTheorems.Conclusion2Family Fm) (h28 : AuxiliaryNormPrimes.OrbitValuationBound Fm cL)
    (h27b : LocalBesselAndTopKernel.TheoremThreePassage Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C1) (h27c : LocalBesselAndTopKernel.FamilyLowestKType Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C2)
    (hN1 : UniformConstantsAndStatements.ConclusionF1 Fm g cN CN) (hN2 : UniformConstantsAndStatements.ConclusionF2 Fm g CE)
    (hCount : FrobeniusProjectedBounds.admF7 Fm g.Cg g.cb g.Cu g.cT g.CT g.C0 c7) :
    FrobeniusProjectedBounds.AdmF Fm At g.Cg g.cb g.Cu g.cT g.CT g.C0 cL cN CN CE c7 :=
  ⟨under_b Fm pExp _ _ _ _ _ _ (fun _ _ h => h),
    under_b Fm p2a _ _ _ _ _ _ (fun _ _ h u u' Φ hS _ hs => h u u' Φ hS hs),
    FrobeniusProjectedBounds.stabiliser_family_of_definite Fm _ _ _ _ _ _ hC' h29,
    FrobeniusProjectedBounds.injectivity_family_of_theorem Fm _ _ _ _ _ _ C1 C2 A cL hCl hC' hA h0 h1 h2 h27b h27c h28,
    FrobeniusProjectedBounds.family_ev_bound_of_source Fm g _ _ hN1, FrobeniusProjectedBounds.norm_bound_family_of_theorem Fm g _ hN2, hCount,
    under_b Fm familyVolumeLowerBound _ _ _ _ _ _ (fun _ _ h => h), under_b Fm pId _ _ _ _ _ _ (fun _ _ h => h),
    under_bG Fm pG _ _ _ _ _ _ (fun _ _ _ h u u' t ht => (h u u' t ht).1)⟩

theorem UniformConstantsAndStatements.family_first_package_of_source (g : UniformConstantsAndStatements.Given) (a : UniformConstantsAndStatements.AdmC)
    (C1 C2 A : ℝ) (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm) (hA : 1 ≤ A) (h0 : 0 ≤ C1) (h1 : C1 ≤ A) (h2 : C2 ≤ A)
    (pExp : PX.ExpF Fm) (p2a : PX.TwoAF Fm) (pMain : PX.MainF Fm g a.CM a.Ce)
    (h29 : NonGenericAndKTwoTheorems.Conclusion1Family Fm a.CNG)
    (hB1 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.RotatedSumBound (Fm.D x i) a.Ch a.Cg a.Cb) (hB2 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.PathWeightComponents (Fm.D x i) a.secondBesselConstant)
    (hB3 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.ConclusionB3 (Fm.D x i) a.Aw a.Ch a.Cgw a.Cbw)
    (h27b : LocalBesselAndTopKernel.TheoremThreePassage Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C1) (h27c : LocalBesselAndTopKernel.FamilyLowestKType Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C2)
    (h28 : AuxiliaryNormPrimes.OrbitValuationBound Fm a.cL) : UniformConstantsAndStatements.FirstFiltrationHypotheses Fm g a :=
  ⟨under_a Fm pExp _ _ _ _ _ _ (fun _ _ h => h),
    under_a Fm p2a _ _ _ _ _ _ (fun _ _ h u u' Φ hS _ hs => h u u' Φ hS hs),
    h29, hB1, hB2, hB3, pMain, UniformConstantsAndStatements.family_count_bound_of_source Fm g C1 C2 A _ hCl hC' hA h0 h1 h2 h27b h27c h28⟩

theorem UniformConstantsAndStatements.family_admissible_package_of_source (g : UniformConstantsAndStatements.Given) (a : UniformConstantsAndStatements.AdmC)
    (pExp : PX.ExpF Fm) (pMain : PX.MainF Fm g a.CM a.Ce) (h29 : NonGenericAndKTwoTheorems.Conclusion1Family Fm a.CNG)
    (hB1 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.RotatedSumBound (Fm.D x i) a.Ch a.Cg a.Cb) (hB2 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.PathWeightComponents (Fm.D x i) a.secondBesselConstant)
    (hB3 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.ConclusionB3 (Fm.D x i) a.Aw a.Ch a.Cgw a.Cbw) : UniformConstantsAndStatements.SecondFiltrationHypotheses Fm g a :=
  ⟨under_a Fm pExp _ _ _ _ _ _ (fun _ _ h => h), h29, hB1, hB2, hB3, pMain⟩

theorem CayleySignature.AdmF_of (c0 : ℝ) (pK : PX.KFinDecayF Fm c0) (h30F : PlaceDegreeData.FamilyLowestKTypeFormula Fm) (h30D : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm)
    (l4 : CayleySignature.admF4 Fm) (l5 : CayleySignature.admF5 Fm) (l6 : CayleySignature.admF6 Fm) (l7 : CayleySignature.admF7 Fm) (l10 : CayleySignature.FamilyRowsCountHypothesis Fm) :
    CayleySignature.AdmF Fm c0 :=
  ⟨CayleySignature.theta_norm_family_of_linked Fm h30F, CayleySignature.theta_condition_family_of_linked Fm h30D, pK, l4, l5, l6, l7, fun _ _ => CayleySignature.capelli_identities_admissible _,
    fun _ _ => CayleySignature.fock_pair_admissible _, l10⟩

end Assembly

section Assembly2

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem AdmissibleBoundsFromSource.AdmF_of (g : UniformConstantsAndStatements.Given) (ca : AdmissibleBoundsFromSource.AdmC)
    (h1 : AdmissibleBoundsFromSource.FirstFiltrationHypotheses Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩ ca)
    (hCount : AdmissibleBoundsFromSource.FamilyRowsCountHypothesis Fm ca.n7 ca.A7 ca.C7 ca.cb7 ca.c7) (pFix : PX.FixedF Fm) :
    AdmissibleBoundsFromSource.AdmF Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩ ca := ⟨h1, hCount, pFix _⟩

theorem LocalBesselAndTopKernel.family_nonvanishing_of_gap (C0 Cg cb Cu cT CT C : ℝ) (h1 : 1 ≤ sCl Fm) (hC : C ≤ sCl Fm) (h : CayleySignature.ConclusionF2 Fm C) :
    LocalBesselAndTopKernel.FamilyVolumeSecond Fm C0 Cg cb Cu cT CT :=
  ⟨0, fun x _ i hy => LocalBesselAndTopKernel.nonvanishing_of_gap_bound _ _ _ _ _ _ _ _ _ _ C hy h1 hC (h x i)⟩

theorem LocalBesselAndTopKernel.family_first_package_of_source (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocalSplitGroups.TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ)
    (Vm : ∀ k r, ValMap k r) (C0 Cg cb Cu cT CT Ca Cq CA CA' settingGapConstant : ℝ) (x₀ : ℝ) (i₀ : Fm.Ix x₀)
    (h1 : 1 ≤ sCl Fm) (h48C : settingGapConstant ≤ sCl Fm)
    (pExp : PX.ExpF Fm) (p2a : PX.TwoAF Fm) (pM : PX.ModelBasics) (pDec : PX.FamilyExpansionWithConstants Fm C0 Cg cb Cu cT CT Ca)
    (pDens : PX.DensF Fm) (pCnt : PX.CntF Fm Z cN) (pForm : PX.FormF Fm X Cw Y Vm C0 Cg cb Cu cT CT)
    (pArith : PX.ArithF Fm cN C0 Cg cb Cu cT CT) (pRk : PX.RanksF Fm C0 Cg cb Cu cT CT)
    (lSchur : LocalBesselAndTopKernel.UnfoldingCount Fm) (lWitt : LocalBesselAndTopKernel.FamilySpectralWeights) (familyMassFirstBound : LocalBesselAndTopKernel.FamilyMultiplicityOneHypothesis Fm) (lWeyl : LocalBesselAndTopKernel.FirstSizeStatement)
    (iSW : LocalBesselAndTopKernel.LocalGenericDensity Fm)
    (h26 : ThinScalesBound.FamilyThinScalesBound Fm Cq) (h26b : JointEigenvalueBoundsFromAnyDatum.OrbitValuationBound Fm Z cN) (h07 : RadialChainStatements.OrbitValuationBound Fm CA CA' 5 Vm) (h48 : CayleySignature.ConclusionF2 Fm settingGapConstant) :
    LocalBesselAndTopKernel.FirstFiltrationHypotheses Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' :=
  ⟨under_a Fm pExp _ _ _ _ _ _ (fun _ _ h => h),
    under_a Fm p2a _ _ _ _ _ _ (fun _ _ h =>
      ⟨fun u u' Φ hS _ hs => h u u' Φ hS hs, Formalism.YangianSpanCharacter.Final.E_GGRatio, Formalism.YangianSpanCharacter.Final.E_GGProd⟩),
    LocalBesselAndTopKernel.local_model_admissible_of_source (Fm.D x₀ i₀) Cq pM (h26 x₀ i₀), fun x i => LocalBesselAndTopKernel.top_bound_of_part_T _ _ (h26 x i), lSchur, lWitt, pDec,
    LocalBesselAndTopKernel.family_nonvanishing_of_gap Fm _ _ _ _ _ _ settingGapConstant h1 h48C h48, familyMassFirstBound,
    fun x i => LocalBesselAndTopKernel.theorem_A_of_source _ _ _ _ (h07 x i), pDens, h26b, pCnt, pForm, pArith, iSW, lWeyl, pRk⟩

theorem LocalBesselAndTopKernel.family_admissible_package_of_source (C0 Cg cb Cu cT CT C3 : ℝ) (pRk : PX.RanksF Fm C0 Cg cb Cu cT CT)
    (lWeyl : LocalBesselAndTopKernel.FirstSizeStatement) (lDTau : LocalBesselAndTopKernel.FamilyMassTheoremTwo) (lDS : LocalBesselAndTopKernel.FamilyDecompositionSumHypothesis Fm C0 Cg cb Cu cT CT)
    (familyMassRatio : LocalBesselAndTopKernel.SecondSizeStatement Fm) (familyMassSecondLine : LocalBesselAndTopKernel.BesselFormLine Fm) (familyTheoremThreeBound : LocalBesselAndTopKernel.FamilyThirdTheoremHypothesis Fm C3) :
    LocalBesselAndTopKernel.SecondFiltrationHypotheses Fm C0 Cg cb Cu cT CT C3 := ⟨lWeyl, familyMassRatio, familyMassSecondLine, pRk, familyTheoremThreeBound, lDTau, lDS⟩

theorem family_mass_bound_of_source (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm)
    (h28b : ∀ Cg cb Cu cT CT C0 : ℝ, VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 1) : NonGenericAndKTwoTheorems.FamilyRankTwoMassHyp Fm := by
  intro Cg cb Cu cT CT C0
  obtain ⟨C, c, x0, H⟩ := h28b Cg cb Cu cT CT C0
  exact ⟨C, x0, fun x hx i => NonGenericAndKTwoTheorems.diagonal_count_bound_of_source _ _ _ _ _ _ _ _ _ _ 1 C c hCl hC' le_rfl (H x hx i _ _)⟩

theorem NonGenericAndKTwoTheorems.AdmF_of (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Cnt.GaugeVol (Fm.D x i))
    (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm)
    (p2a : PX.TwoAgF Fm) (pExp : PX.ExpF Fm) (pId : PX.IdCellF Fm) (familyVolumeLowerBound : PX.FamilyVanishingCondition Fm) (pG : PX.GDrF Fm At)
    (pCells : PX.CellsF Fm At) (pSize : PX.SizeF Fm) (pVol : PX.MassVolF Fm Gv)
    (lSchur : NonGenericAndKTwoTheorems.adm7) (lMink : NonGenericAndKTwoTheorems.adm11) (familyMassRatio : NonGenericAndKTwoTheorems.FamilyMassFirstHypothesis Fm) (familyMassSecondLine : NonGenericAndKTwoTheorems.FamilyMassSecondHypothesis Fm)
    (h71 : ∀ Cg cb Cu cT CT C0 : ℝ, FrobeniusProjectedBounds.ConclusionF1 Fm At Cg cb Cu cT CT C0)
    (h28b1 : ∀ Cg cb Cu cT CT C0 : ℝ, VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 1)
    (h28b2 : VanishingOnXAndXPlusMass.Conclusion2Family Fm) (h28b3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm) (familyMassExponential : NonGenericAndKTwoTheorems.FamilyMassLatticeBound Fm) : NonGenericAndKTwoTheorems.AdmF Fm At Gv :=
  ⟨fun _ _ _ _ _ _ => under_b Fm p2a _ _ _ _ _ _ (fun _ _ h => h),
    fun _ _ _ _ _ _ => under_b Fm pExp _ _ _ _ _ _ (fun _ _ h => h),
    fun Cg cb Cu cT CT C0 => OwnEv.mono
      (fun _ _ _ _ hh hx => NonGenericAndKTwoTheorems.integrality_of_commutation _ _ _ _ _ _ _ _ _ _ _ (fun hy => hh.1 ⟨hy.2.1, hy.1, hy.2.2⟩) (hh.2 hx))
      (OwnEv.and (pId C0 Cg cb Cu cT CT) (h71 Cg cb Cu cT CT C0)),
    fun _ _ _ _ _ _ => under_b Fm familyVolumeLowerBound _ _ _ _ _ _ (fun _ _ h => h),
    fun _ _ _ _ _ _ => under_bG Fm pG _ _ _ _ _ _ (fun _ _ _ h => h),
    pCells, lSchur, pSize, familyMassRatio, familyMassSecondLine, family_mass_bound_of_source Fm hCl hC' h28b1, pVol, h28b2, h28b3, lMink, familyMassExponential⟩

theorem LatticeIndexAndWeightTheory.AdmF_of (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
    (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm)
    (p2a : PX.TwoAgF Fm) (pExp : PX.ExpF Fm) (pId : PX.IdCellF Fm) (familyVolumeLowerBound : PX.FamilyVanishingCondition Fm)
    (pCells : PX.CellsF Fm At) (pSize : PX.SizeF Fm) (pVol : PX.MassVolGF Fm) (pDu : PX.DuMassF Fm)
    (lSchur : LatticeIndexAndWeightTheory.adm8) (lMink : LatticeIndexAndWeightTheory.adm5) (familyMassRatio : LatticeIndexAndWeightTheory.FamilyMassFirstHypothesis Fm) (familyMassSecondLine : LatticeIndexAndWeightTheory.FamilyMassSecondHypothesis Fm)
    (h71 : ∀ Cg cb Cu cT CT C0 : ℝ, FrobeniusProjectedBounds.ConclusionF1 Fm At Cg cb Cu cT CT C0)
    (h28b1 : ∀ Cg cb Cu cT CT C0 : ℝ, VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 1)
    (h28b2 : VanishingOnXAndXPlusMass.Conclusion2Family Fm) (h28b3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm) (familyMassExponential : LatticeIndexAndWeightTheory.FamilyMassLatticeBound Fm) : LatticeIndexAndWeightTheory.AdmF Fm At :=
  ⟨fun _ _ _ _ _ _ => under_b Fm p2a _ _ _ _ _ _ (fun _ _ h => h),
    fun Cg cb Cu cT CT C0 Cθ C1 => by
      obtain ⟨cq, Cq, CH, hcq, hCq, h⟩ := pSize Cg cb Cu cT CT C0 Cθ
      exact ⟨cq, Cq, CH, hcq, hCq, h C1⟩,
    fun C0 Cg cb Cu cT CT => OwnEv.mono (fun _ _ _ _ hh hy => ⟨hh.1 ⟨hy.2.1, hy.1, hy.2.2⟩, hh.2 ⟨hy.2.1, hy.1, hy.2.2⟩⟩)
      (OwnEv.and (pExp CT C0 Cg cb Cu cT) (pId CT C0 Cg cb Cu cT)),
    lMink, LatticeIndexAndWeightTheory.norm_bound_family_of_theorem Fm At h71, pCells, lSchur, familyMassRatio, familyMassSecondLine, family_mass_bound_of_source Fm hCl hC' h28b1, pVol, h28b2, h28b3,
    fun _ _ _ _ _ _ => under_b Fm familyVolumeLowerBound _ _ _ _ _ _ (fun _ _ h => h), pDu, familyMassExponential⟩

end Assembly2

section All

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem S0.family_statements_all (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Cnt.GaugeVol (Fm.D x i))
    (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' Cw)
    (Zl : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocalSplitGroups.TermLocs (Fm.D x i) (At x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) (Vm : ∀ k r, ValMap k r)
    (g : UniformConstantsAndStatements.Given) (ca : AdmissibleBoundsFromSource.AdmC) (a : UniformConstantsAndStatements.AdmC) (Ca Cq C3 C3' C4 settingGapConstant Ch Cβ Cs Cq0 Cr C2 : ℝ) (x₀ : ℝ) (i₀ : Fm.Ix x₀)

    (hGiv : LocalBesselAndTopKernel.GivOk g.C0 g.Cg g.cb g.Cu g.cT g.CT) (hca : ca.Ok g.Cg) (hGam : max ca.CE ca.CN + 1 ≤ Fm.CGam)
    (hCl : 2 < sCl Fm) (hC' : 1 ≤ sC' Fm) (hC1 : 0 ≤ ca.C1) (h48C : settingGapConstant ≤ sCl Fm)
    (hCh : 0 ≤ Ch) (hβ : 1 ≤ Cβ) (hq0 : 0 < Cq0) (hr : 0 < Cr)

    (s71a : ∀ Cg cb Cu cT CT C0 : ℝ, FrobeniusProjectedBounds.FamilyGlobalDerivation Fm At Cg cb Cu cT CT C0)
    (s71b : FrobeniusProjectedBounds.SecondPartFamily Fm At g.Cg g.cb g.Cu g.cT g.CT g.C0 ca.cL ca.cN ca.CN ca.CE)
    (s27a : LocalBesselAndTopKernel.PeriodFamilyStatement Fm At Cw Y Zl cN Vm g.C0 g.Cg g.cb g.Cu g.cT g.CT Ca Cq ca.CA ca.CA' ca.Ce)
    (s27b : LocalBesselAndTopKernel.DeterminantValueFamily Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT C3 ca.C1 ca.C2 C3' C4 ca.c5 ca.CA ca.ep0 ca.CV)
    (s29n : NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm a.CNG) (s29k : NonGenericAndKTwoTheorems.FamilyNonIdentityTermSummabilityOfAdmissible Fm At Gv)
    (familyGenericCountBound : UniformConstantsAndStatements.PeriodFamilyStatement Fm g a ca.cN ca.CN) (familyNongenericCountBound : UniformConstantsAndStatements.DeterminantValueFamily Fm g a ca.CE)
    (s76 : AdmissibleBoundsFromSource.PeriodFamilyStatement Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩ ca) (s48 : CayleySignature.DeterminantValueFamily Fm settingGapConstant)

    (h07 : RadialChainStatements.OrbitValuationBound Fm ca.CA ca.CA' 5 Vm) (h26 : ThinScalesBound.FamilyThinScalesBound Fm Cq) (h26b : JointEigenvalueBoundsFromAnyDatum.OrbitValuationBound Fm Zl cN)
    (h30 : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm)
    (h28 : AuxiliaryNormPrimes.OrbitValuationBound Fm ca.cL) (h28' : AuxiliaryNormPrimes.OrbitValuationBound Fm a.cL)
    (h28b1 : ∀ Cg cb Cu cT CT C0 : ℝ, VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 1)
    (h28b2 : VanishingOnXAndXPlusMass.Conclusion2Family Fm) (h28b3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm)
    (hB1 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.RotatedSumBound (Fm.D x i) a.Ch a.Cg a.Cb) (hB2 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.PathWeightComponents (Fm.D x i) a.secondBesselConstant)
    (hB3 : ∀ x (i : Fm.Ix x), OnePlaceEstimates.ConclusionB3 (Fm.D x i) a.Aw a.Ch a.Cgw a.Cbw)
    (h93 : OnePlaceEstimates.FamilySubmultiplicativeNorm Fm Ch Cs Cq0 Cr C2)

    (pExp : PX.ExpF Fm) (pId : PX.IdCellF Fm) (p2a : PX.TwoAF Fm) (p2ag : PX.TwoAgF Fm) (familyVolumeLowerBound : PX.FamilyVanishingCondition Fm)
    (pG : PX.GDrF Fm At) (pIdG : PX.FamilyIdentityCondition Fm) (familyStandingLowerBound : PX.FamilyFirstSumAtLeastOne Fm) (pAbs : PX.PairAbsF Fm) (pCells : PX.CellsF Fm At)
    (pVol : PX.MassVolF Fm Gv) (pMain : PX.MainF Fm g a.CM a.Ce)
    (pM : PX.ModelBasics) (pDec : PX.FamilyExpansionWithConstants Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT Ca)
    (pDens : PX.DensF Fm) (pCnt : PX.CntF Fm Zl cN) (pForm : PX.FormF Fm At Cw Y Vm g.C0 g.Cg g.cb g.Cu g.cT g.CT)
    (pArith : PX.ArithF Fm cN g.C0 g.Cg g.cb g.Cu g.cT g.CT) (familySettingGapBound : PX.FamilyFunctionalOrderWithConstant Fm settingGapConstant) (pRk : PX.RanksF Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT)

    (bMom : PX.Mom Fm) (bHaar : PX.SHaar Fm)
    (bStd : ∀ Cg cb Cu cT CT C0 : ℝ, PX.StdHypS Fm Cg cb Cu cT CT C0 Ch Cβ)
    (bTF : ∀ Cg cb Cu cT CT C0 : ℝ, PX.TFrame Fm Cg cb Cu cT CT C0)

    (familyWeylLawBound : AdmissibleBoundsFromSource.FamilyWeylDimension Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩) (familySchurOrthogonality : LocalBesselAndTopKernel.UnfoldingCount Fm) (lWitt : LocalBesselAndTopKernel.FamilySpectralWeights)
    (familyMassFirstBound : LocalBesselAndTopKernel.FamilyMultiplicityOneHypothesis Fm) (weylLawBound : LocalBesselAndTopKernel.FirstSizeStatement) (lDTau : LocalBesselAndTopKernel.FamilyMassTheoremTwo)
    (lDS : LocalBesselAndTopKernel.FamilyDecompositionSumHypothesis Fm g.C0 g.Cg g.cb g.Cu g.cT g.CT) (schurLemma : NonGenericAndKTwoTheorems.adm7) (lMink : NonGenericAndKTwoTheorems.adm11) (familySchurSetting : CayleySignature.admF6 Fm)

    (familyMassIdentity : AdmissibleBoundsFromSource.FamilyTwelfthHypothesis) (familyMassRatio : LocalBesselAndTopKernel.SecondSizeStatement Fm) (familyMassSecondLine : LocalBesselAndTopKernel.BesselFormLine Fm) (familyTheoremThreeBound : LocalBesselAndTopKernel.FamilyThirdTheoremHypothesis Fm C3)
    (iM1' : NonGenericAndKTwoTheorems.FamilyMassFirstHypothesis Fm) (iM2' : NonGenericAndKTwoTheorems.FamilyMassSecondHypothesis Fm) (iSW : LocalBesselAndTopKernel.LocalGenericDensity Fm) (familyMassExponential : NonGenericAndKTwoTheorems.FamilyMassLatticeBound Fm) :
    AdmissibleBoundsFromSource.ConclusionF1 Fm ⟨g.C0, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩ ∧ FrobeniusProjectedBounds.ConclusionF2 Fm g.Cg g.cb g.Cu g.cT g.CT g.C0 := by
  have hca' : ca.Ok g.Cg := hca
  obtain ⟨hA1, hA2, hA3, hcL, hcN, hCN, hCE, -⟩ := hca
  have h71 : ∀ Cg cb Cu cT CT C0 : ℝ, FrobeniusProjectedBounds.ConclusionF1 Fm At Cg cb Cu cT CT C0 := fun Cg cb Cu cT CT C0 =>
    s71a Cg cb Cu cT CT C0 ⟨under_b Fm pExp _ _ _ _ _ _ (fun _ _ h => h), under_b Fm familyVolumeLowerBound _ _ _ _ _ _ (fun _ _ h => h),
      under_b Fm pId _ _ _ _ _ _ (fun _ _ h => h)⟩
  obtain ⟨h27a, h27b, h27c, -, -, h27f, h27g⟩ :=
    s27b hGiv (LocalBesselAndTopKernel.family_admissible_package_of_source Fm _ _ _ _ _ _ _ pRk weylLawBound lDTau lDS familyMassRatio familyMassSecondLine familyTheoremThreeBound)
  obtain ⟨hK2, hK3⟩ := s29k (NonGenericAndKTwoTheorems.AdmF_of Fm At Gv hCl hC' p2ag pExp pId familyVolumeLowerBound pG pCells
    (NonGenericAndKTwoTheorems.family_moment_bounds_of_source Fm Ch Cβ Cs Cq0 Cr C2 hCh hβ hq0 hr h93 bMom bHaar bStd bTF) pVol schurLemma lMink iM1' iM2'
    h71 h28b1 h28b2 h28b3 familyMassExponential)
  have hN1 := familyGenericCountBound (UniformConstantsAndStatements.family_first_package_of_source Fm g a ca.C1 ca.C2 ca.A5 hCl hC' hA1 hC1 hA2 hA3 pExp p2a pMain s29n hB1 hB2 hB3
    h27b h27c h28')
  have hN2 := familyNongenericCountBound (UniformConstantsAndStatements.family_admissible_package_of_source Fm g a pExp pMain s29n hB1 hB2 hB3)
  have h27 := s27a hGiv (LocalBesselAndTopKernel.family_first_package_of_source Fm At Cw Y Zl cN Vm _ _ _ _ _ _ _ _ _ _ settingGapConstant x₀ i₀ (by linarith) h48C pExp p2a pM pDec
    pDens pCnt pForm pArith pRk familySchurOrthogonality lWitt familyMassFirstBound weylLawBound iSW h26 h26b h07
    (s48 familySettingGapBound (CayleySignature.theta_condition_family_of_linked Fm h30) familySchurSetting))
  refine ⟨s76 hGiv hca' hGam (AdmissibleBoundsFromSource.family_first_package_of_source Fm g ca pExp pId p2a familyVolumeLowerBound pIdG familyStandingLowerBound pAbs familyWeylLawBound familyMassIdentity hK2 hK3 h28 hN1 hN2 h27
    h27a h27b h27c h27f h27g), ?_⟩
  exact s71b ⟨hcL, hcN, hCN, hCE, hGam⟩
    ⟨under_b Fm pExp _ _ _ _ _ _ (fun _ _ h => h), under_b Fm p2a _ _ _ _ _ _ (fun _ _ h u u' Φ hS _ hs => h u u' Φ hS hs),
      FrobeniusProjectedBounds.injectivity_family_of_theorem Fm _ _ _ _ _ _ ca.C1 ca.C2 ca.A5 ca.cL hCl hC' hA1 hC1 hA2 hA3 h27b h27c h28,
      FrobeniusProjectedBounds.family_ev_bound_of_source Fm g _ _ hN1, FrobeniusProjectedBounds.norm_bound_family_of_theorem Fm g _ hN2⟩ (h71 _ _ _ _ _ _)

end All

end Formalism.MainNotions

section S8c

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.CayleySignature

namespace Formalism.MainNotions.ConjugationAmplitude

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : ThetaX D)

theorem conjAF_zero (V : HSp D) : X.conjAF V 0 = 0 := by
  have := X.conjAF_smul V 0 0
  simpa using this

def dvSub (P : TPar D) (j : ℕ) : Submodule ℂ (X.AF (X.Ys P.t j)) where
  carrier := {F | F ∈ X.cusp _ ∧ IsDv X P j F}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, ?_⟩
    unfold IsDv at *
    rw [X.conjAF_add]
    exact add_mem ha' hb'
  zero_mem' := by
    refine ⟨zero_mem _, ?_⟩
    unfold IsDv
    rw [conjAF_zero]
    exact zero_mem _
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Submodule.smul_mem _ c ha, ?_⟩
    unfold IsDv at *
    rw [X.conjAF_smul]
    exact Submodule.smul_mem _ _ ha'

def Q (P : TPar D) (μ : ℕ → X.Chr) (π : ∀ j : ℕ, Submodule ℂ (X.AF (X.Xs P.t j))) (j : ℕ) : Prop :=
  ∃ (F : ∀ j : ℕ, X.cusp (X.Ys P.t j)) (Φ : ∀ j : ℕ, X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j)),
    IsDv X P D.R.m (F D.R.m : X.AF (X.Ys P.t D.R.m)) ∧
    (∀ i : ℕ, j ≤ i → i < D.R.m → Φ i ∈ X.fact _ _ ∧ Φ i ∈ X.kfin _ _ ∧
      ((F i : X.cusp (X.Ys P.t i)) : X.AF (X.Ys P.t i)) = vth X P.t μ i (Φ i) (F (i + 1)) ∧
      IsDv X P i (F i : X.AF (X.Ys P.t i))) ∧
    IsDv X P j (F j : X.AF (X.Ys P.t j)) ∧ ∃ φ ∈ π j, PerNZ X P.t j φ (F j)

end Formalism.MainNotions.ConjugationAmplitude

end S8c
