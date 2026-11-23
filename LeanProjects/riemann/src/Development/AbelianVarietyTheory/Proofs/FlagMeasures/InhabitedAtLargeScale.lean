import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHostWithPrimesCyclicTwoPower
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN

noncomputable section

namespace GlobalTheory.Diag.PG.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem exists_hc (R : Ranks) (Del h : ℕ) (U W B : ℤ) (hD : 1 ≤ Del) (hh : R.t + 3 ≤ 2 * h)
    (hU : ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ U) (hW : W ≤ 0) (hB : 1 ≤ B + W) :
    ∃ P : HCParam R, (∀ i, P.v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * Del)) ∧
      (∀ hk, P.u ⟨0, hk⟩ = U + 1 / 2) ∧ (∀ hk, P.u ⟨R.k - 1, hk⟩ = W - 1 / 2) ∧
      (∀ (l : ℕ) (hl : l < R.k - 2), P.u ⟨l + 1, by omega⟩ = P.v ⟨l, by omega⟩ - 1 / 2) ∧
      (∀ j, P.b j = B + 2 * h * j.1) ∧ ∀ j, P.e j = B + 2 * h * j.1 + h := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hD' : (1 : ℚ) ≤ Del := by exact_mod_cast hD
  have hh' : (R.t : ℚ) + 3 ≤ 2 * h := by exact_mod_cast hh
  have hU' : ((R.k - 2 : ℕ) : ℚ) * (4 * Del) ≤ U := by exact_mod_cast hU
  have hW' : (W : ℚ) ≤ 0 := by exact_mod_cast hW
  have hB' : (1 : ℚ) ≤ B + W := by exact_mod_cast hB
  refine ⟨{ u := fun i => if i.1 = 0 then U + 1 / 2 else if i.1 = R.k - 1 then W - 1 / 2
                else ((R.k - 1 - i.1 : ℕ) : ℚ) * (4 * Del) - 1 / 2
            v := fun i => ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * Del)
            b := fun j => B + 2 * h * j.1
            e := fun j => B + 2 * h * j.1 + h
            u_gt_v := ?_, v_gt_u := ?_, u_last_gt := ?_, gap_be := ?_, gap_eb := ?_, e_int := ?_,
            u_half := ?_, v_int := ?_, b_int := ?_ }, fun _ => rfl, fun _ => by simp, fun _ => ?_, fun l hl => ?_,
    fun _ => rfl, fun _ => rfl⟩
  · intro i
    have hi := i.2
    by_cases h0 : i.1 = 0
    · simp only [h0, if_true, Nat.sub_zero]; linarith
    · have h1 : i.1 ≠ R.k - 1 := by omega
      simp only [if_neg h0, if_neg h1]
      rw [show R.k - 1 - i.1 = (R.k - 2 - i.1) + 1 by omega]
      push_cast; linarith
  · intro i
    have hi := i.2
    have h0 : i.1 + 1 ≠ 0 := by omega
    simp only [if_neg h0]
    split_ifs with h1
    · have : (0 : ℚ) ≤ ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * Del) := by positivity
      linarith
    · rw [show R.k - 1 - (i.1 + 1) = R.k - 2 - i.1 by omega]; linarith
  · intro _ _
    have h0 : R.k - 1 ≠ 0 := by omega
    simp only [if_neg h0, if_true]
    push_cast; linarith
  · intro j; linarith
  · intro j _; push_cast; linarith
  · intro j; exact ⟨B + 2 * h * j.1 + h, by push_cast; ring⟩
  · intro i
    split_ifs
    · exact ⟨U, rfl⟩
    · exact ⟨W - 1, by push_cast; ring⟩
    · exact ⟨((R.k - 1 - i.1 : ℕ) : ℤ) * (4 * Del) - 1, by push_cast; ring⟩
  · intro i; exact ⟨((R.k - 2 - i.1 : ℕ) : ℤ) * (4 * Del), by push_cast; ring⟩
  · intro j; exact ⟨B + 2 * h * j.1, by push_cast; ring⟩
  · have h0 : R.k - 1 ≠ 0 := by omega
    simp only [if_neg h0, if_true]
  · have h0 : l + 1 ≠ 0 := by omega
    have h1 : l + 1 ≠ R.k - 1 := by omega
    simp only [if_neg h0, if_neg h1]
    rw [show R.k - 1 - (l + 1) = R.k - 2 - l by omega]

theorem large (eps K : ℝ) (he : 0 < eps) (hK : 1000 ≤ K) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 1000000 ≤ x ∧ 1 ≤ Real.log x ∧ K * Real.log x ≤ x ^ (eps / 10) ∧ 1000 ≤ x ^ (eps / 10) ∧
      (∀ c, c ≤ K → x ^ c ≤ Real.exp (x ^ (eps / 10))) ∧
      ∀ a b C : ℝ, C ≤ 1000 → a + eps / 10 ≤ b → C * x ^ a ≤ x ^ b := by
  obtain ⟨x1, h⟩ : ∃ x1 : ℝ, ∀ x, x1 ≤ x → K * Real.log x ≤ x ^ (eps / 10) := by
    have hK0 : 0 < K := by linarith
    obtain ⟨x0, h0⟩ := Filter.eventually_atTop.1
      ((isLittleO_log_rpow_atTop (show 0 < eps / 10 by linarith)).bound (inv_pos.2 hK0))
    refine ⟨max x0 1, fun x hx => ?_⟩
    have h1 := h0 x (le_of_max_le_left hx)
    have hx1 : 1 ≤ x := le_of_max_le_right hx
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (by positivity)] at h1
    calc K * Real.log x ≤ K * (K⁻¹ * x ^ (eps / 10)) := by gcongr
      _ = x ^ (eps / 10) := by field_simp
  refine ⟨max x1 1000000, fun x hx => ?_⟩
  have h1 := h x (le_of_max_le_left hx)
  have h6 : 1000000 ≤ x := le_of_max_le_right hx
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  have hy : 1000 ≤ x ^ (eps / 10) := by nlinarith
  refine ⟨h6, hl, h1, hy, fun c hc => ?_, fun a b C hC hab => ?_⟩
  · rw [Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.2 (by nlinarith)
  · calc C * x ^ a ≤ x ^ (eps / 10) * x ^ a := mul_le_mul_of_nonneg_right (hC.trans hy) (by positivity)
      _ = x ^ (a + eps / 10) := by rw [Real.rpow_add hx0, mul_comm]
      _ ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le (by linarith) hab

def delOf (x eps CD : ℝ) (R : Ranks) : ℕ := ⌈((R.k : ℝ) * R.f * x ^ eps) ^ CD⌉₊

theorem rankNums_of_rankVal (eps CD : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hCD : 0 ≤ CD) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      1 ≤ delOf s.x eps CD R ∧ (delOf s.x eps CD R : ℝ) ≤ s.x ^ (9 * CD + 1) ∧
      ∀ lrd, Real.log 2 ≤ lrd → lrd ≤ s.x ^ (eps / 2) →
        RankNums s.x eps CD R.m R.f R.k lrd (delOf s.x eps CD R) := by
  obtain ⟨x1, hb⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x2, hl⟩ := large eps (1000 + 9 * CD) h0 (by linarith)
  refine ⟨max x1 x2, fun s R hs hx hR => ?_⟩
  obtain ⟨bf, -, br, kr, -, bL, scaledRowVectorOperator, -, -, -, -, -, -, -, -, ml, mu⟩ := hb s R hs (le_of_max_le_left hx) hR
  obtain ⟨h6, hlog, hK, hy, -, ab⟩ := hl s.x (le_of_max_le_right hx)
  obtain ⟨⟨n1, n2⟩, -, ⟨k1, -⟩, -⟩ := hR
  unfold Scale.L at bL scaledRowVectorOperator
  rw [hs] at bL scaledRowVectorOperator ml mu n1 n2 k1
  set x := s.x
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have mono : ∀ {a b : ℝ}, a ≤ b → x ^ a ≤ x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have bk : (R.k : ℝ) ≤ x ^ (5 : ℝ) := le_trans (by exact_mod_cast kr) br
  have hk0 : (0 : ℝ) < R.k := by have := R.m_add_three_le_k; exact_mod_cast (by omega : 0 < R.k)
  have hf0 : (0 : ℝ) < R.f := by have := R.ord_pos; exact_mod_cast (show 0 < 2 * R.ord by omega)
  have hm0 : (0 : ℝ) ≤ R.m := by positivity
  have hp : (0 : ℝ) < ((R.k : ℝ) * R.f * x ^ eps) ^ CD := by positivity
  have hD1 : 1 ≤ delOf x eps CD R := Nat.ceil_pos.2 hp
  have hD2 : (delOf x eps CD R : ℝ) ≤ x ^ (9 * CD + 1) := by
    have a1 : (R.k : ℝ) * R.f * x ^ eps ≤ x ^ (9 : ℝ) := by
      rw [show (9 : ℝ) = 5 + 3 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      gcongr
    have a2 : ((R.k : ℝ) * R.f * x ^ eps) ^ CD ≤ x ^ (9 * CD) := by
      rw [Real.rpow_mul hx0.le]; gcongr
    have a3 := Nat.ceil_lt_add_one hp.le
    have a4 : 1 ≤ x ^ (9 * CD) := Real.one_le_rpow hx1 (by linarith)
    have a5 := ab (9 * CD) (9 * CD + 1) 2 (by norm_num) (by linarith)
    unfold delOf; linarith
  have mp : ∀ j : ℕ, (R.m : ℝ) ^ j ≤ 2 ^ j * x ^ ((1 / 2 - eps / 16) * j) := fun j => by
    rw [Real.rpow_mul_natCast hx0.le, ← mul_pow]; gcongr
  refine ⟨hD1, hD2, fun lrd l1 l2 => ⟨(mono (by linarith)).trans ml, ?_, by exact_mod_cast R.f_le_k, ?_, bk, l1, l2,
    Nat.le_ceil _, ?_⟩⟩
  · have a1 := mp 4
    have a2 := ab ((1 / 2 - eps / 16) * (4 : ℕ)) (2 + 8 * eps) (2 ^ 4) (by norm_num) (by push_cast; linarith)
    have : 0 ≤ x ^ (2 + 8 * eps) := by positivity
    linarith
  · have a1 := mp 5
    have a2 := ab (eps / 2 + ((1 / 2 - eps / 16) * (5 : ℕ) + (2 + 8 * eps) + eps)) (9 / 2 + 10 * eps) 128 (by norm_num)
      (by push_cast; linarith)
    rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0 _ (2 + 8 * eps)] at a2
    have a3 : (R.f : ℝ) ≤ 4 * x ^ (2 + 8 * eps) := by linarith
    calc x ^ (eps / 2) * ((R.m : ℝ) ^ 5 * R.f * x ^ eps)
        ≤ x ^ (eps / 2) * ((2 ^ 5 * x ^ ((1 / 2 - eps / 16) * (5 : ℕ))) * (4 * x ^ (2 + 8 * eps)) * x ^ eps) := by gcongr
      _ ≤ (R.k : ℝ) := by linarith
  · have a1 : Real.log (delOf x eps CD R : ℝ) ≤ (9 * CD + 1) * Real.log x := by
      rw [← Real.log_rpow hx0]
      exact Real.log_le_log (by exact_mod_cast hD1) hD2
    have a2 : x ^ (eps / 10) ≤ x ^ (eps / 2) := mono (by linarith)
    nlinarith

theorem exists_rankNums (eps CD : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hCD : 0 ≤ CD) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∃ m e k Del : ℕ, Even m ∧ Even k ∧
      RankNums x eps CD m ((2 * 2 ^ e : ℕ) : ℝ) k 1 Del ∧
      ∀ lrd, Real.log 2 ≤ lrd → lrd ≤ x ^ (eps / 2) → RankNums x eps CD m ((2 * 2 ^ e : ℕ) : ℝ) k lrd Del := by
  obtain ⟨x1, h⟩ := rankNums_of_rankVal eps CD h0 h1 hCD
  obtain ⟨x2, hR⟩ := exists_ranks_cyclic_frame eps h0 h1
  refine ⟨max (max x1 x2) 2, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_of_max_le_right hx
  let s : Scale := ⟨x, eps, by linarith, h0, h1, 1, le_rfl⟩
  obtain ⟨R, hV, -, hφ⟩ := hR s rfl (le_of_max_le_right (le_of_max_le_left hx))
  obtain ⟨-, -, hn⟩ := h s R rfl (le_of_max_le_left (le_of_max_le_left hx)) hV
  rw [show (R.f : ℝ) = ((2 * 2 ^ R.e : ℕ) : ℝ) by rw [← (UpperTheory.Host.cyclic_two_power_frame_facts hφ).2.2]; rfl] at hn
  refine ⟨R.m, R.e, R.k, delOf x eps CD R, R.m_even, R.k_even, hn 1 ?_ ?_, hn⟩
  · have := Real.log_two_lt_d9; linarith
  · exact Real.one_le_rpow (by show 1 ≤ x; linarith) (by linarith)

theorem rd_bounds {R : Ranks} (H : Host R) : 2 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) * H.q * H.d :=
  ⟨UpperTheory.Ram.Rd.two_le_rdE H, UpperTheory.Ram.Rd.rdE_le_cond H⟩

theorem exists_host_level_gen (eps c c' : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hc : 1 / 2 ≤ c) (hc' : c' = 2 * c) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → 2 ≤ R.e →
      R.toFrame = Formalism.HC.cyclicFrame R.e →
      ∃ (H : Host R) (T : ℕ) (π : 𝓞 H.E), T.Prime ∧ T ∈ H.levelPrimes ∧ (T ≠ H.pde ∧ T ≠ H.pde') ∧ (π : H.E) ∈ H.K ∧
        (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
        (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)} ∧
        (∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) ∧ THyp H ∧ H.TT.Nonempty ∧ H.T2.Nonempty ∧
        H.Lw = Lwv s ∧ (⌊s.x ^ (eps / 5)⌋₊ ≤ H.splitBound ∧ SplitLab H s.x eps) ∧ Real.log H.rdE ≤ s.x ^ (eps / 2) ∧
        (∀ i, ((R.k : ℝ) * bx s.x eps) ^ 8 ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ bx s.x eps ^ (9 : ℝ)) ∧
        bx s.x eps ^ (c * (R.m : ℝ)) ≤ (T : ℝ) ∧ (T : ℝ) ≤ bx s.x eps ^ (c' * (R.m : ℝ)) ∧
        Real.sqrt (Real.exp (s.x ^ (eps / 5) * Real.log s.x ^ 2)) < H.d := by
  obtain ⟨x1, hH⟩ := UpperTheory.Host.exists_host_with_level_prime eps c h0 h1 hc
  obtain ⟨x2, hl⟩ := large eps 1000 h0 le_rfl
  refine ⟨max x1 x2, fun s R hs hx hR he hφ => ?_⟩
  obtain ⟨H, T, π, Tp, Tl, Tne, pK, pn, pc, gm, bb, tt, t2, -, lw, sp, qs, wp, hlg, gw, T1, T2⟩ :=
    hH s R hs (le_of_max_le_left hx) hR he hφ
  subst hs hc'
  obtain ⟨h6, hlog, hK, hy, -, -⟩ := hl s.x (le_of_max_le_right hx)
  obtain ⟨-, ho, hn⟩ := UpperTheory.Host.cyclic_two_power_frame_facts hφ
  have hx0 : 0 < s.x := by linarith
  have h100 : 1 ≤ s.x ^ (s.eps / 100) := Real.one_le_rpow (by linarith) (by linarith)
  have hsp := fun i => GlobalTheory.HostSplit.split_of_one_mod R H _ (H.g_prime i) (gm i)
  refine ⟨H, T, π, Tp, Tl, Tne, pK, pn, pc, fun i => (hsp i).1, ⟨gm, bb, fun i => ?_⟩, tt ▸ Finset.univ_nonempty,
    t2 ▸ Finset.singleton_nonempty 0, lw, ⟨sp.ge, SplitLab.of_one sp.ge ?_ ?_⟩, ?_, fun i => ⟨(gw i).1, ?_⟩, T1, T2, ?_⟩
  · obtain ⟨c1, -, -, c4⟩ : H.g i ∉ H.small ∧ H.g i ≠ H.q ∧ H.g i ≠ H.d ∧ jacobiSym (-(H.d : ℤ)) (H.g i) = 1 := by
      have h := (hsp i).2
      unfold Host.cls primeClass at h
      split_ifs at h with c1 c2 c3 c4
      exact ⟨c1, c2, c3, c4⟩
    exact ⟨fun h => c1 (h ▸ H.two_mem_small), c4⟩
  · rw [ho]; simpa using h100
  · rw [qs, hn]
    push_cast
    rw [pow_add]
    have : (0 : ℝ) < 2 ^ R.e := by positivity
    nlinarith
  · obtain ⟨r1, r2⟩ := rd_bounds H
    have a1 := (Real.log_le_log (by linarith) r2).trans hlg
    have a2 : Real.log s.x ^ 2 ≤ (s.x ^ (s.eps / 10)) ^ 2 := by gcongr; linarith
    have a3 : s.x ^ (s.eps / 2) = s.x ^ (s.eps / 10) * s.x ^ (s.eps / 5) * (s.x ^ (s.eps / 10)) ^ 2 := by
      rw [sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    rw [a3]
    refine a1.trans ?_
    gcongr
    linarith
  · have := (gw i).2.2
    rw [← Real.rpow_natCast] at this
    exact_mod_cast this
  · rw [← Real.exp_half, ← Real.lt_log_iff_exp_lt (by exact_mod_cast H.hyp.2.1.pos)]
    exact wp.d_lo

theorem exists_host_level (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → 2 ≤ R.e →
      R.toFrame = Formalism.HC.cyclicFrame R.e →
      ∃ (H : Host R) (T : ℕ) (π : 𝓞 H.E), T.Prime ∧ T ∈ H.levelPrimes ∧ (T ≠ H.pde ∧ T ≠ H.pde') ∧ (π : H.E) ∈ H.K ∧
        (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
        (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)} ∧
        (∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) ∧ THyp H ∧ H.TT.Nonempty ∧ H.T2.Nonempty ∧
        H.Lw = Lwv s ∧ (⌊s.x ^ (eps / 5)⌋₊ ≤ H.splitBound ∧ SplitLab H s.x eps) ∧ Real.log H.rdE ≤ s.x ^ (eps / 2) ∧
        (∀ i, ((R.k : ℝ) * bx s.x eps) ^ 8 ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ bx s.x eps ^ (9 : ℝ)) ∧
        bx s.x eps ^ ((1 / 2 : ℝ) * (R.m : ℝ)) ≤ (T : ℝ) ∧ (T : ℝ) ≤ bx s.x eps ^ ((1 : ℝ) * (R.m : ℝ)) := by
  obtain ⟨x0, h⟩ := exists_host_level_gen eps (1 / 2) 1 h0 h1 le_rfl (by norm_num)
  refine ⟨x0, fun s R hs hx hR he hφ => ?_⟩
  obtain ⟨H, T, π, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, -⟩ := h s R hs hx hR he hφ
  exact ⟨H, T, π, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩

theorem weight_sizes (x eps : ℝ) (he : 0 < eps) (hx : 1 ≤ x) (hy : 1000 ≤ x ^ (eps / 10))
    (hp : x ^ ((11 : ℝ) / 2) ≤ Real.exp (x ^ (eps / 10))) :
    10 ≤ Real.exp (x ^ (eps / 10)) ∧ Real.exp (x ^ (eps / 10)) * Real.exp (x ^ (eps / 10)) ≤ Real.sqrt (bx x eps) ∧
      Real.sqrt (bx x eps) ≤ bpC x eps / x ∧ bpC x eps ≤ aC x eps ∧ bx x eps ≤ aC x eps ∧
      aC x eps ≤ Real.exp (x ^ (eps / 10)) * bx x eps := by
  have hx0 : 0 < x := by linarith
  have mono : ∀ {a b : ℝ}, a ≤ b → x ^ a ≤ x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hx h
  have hb : 0 < bx x eps := Real.exp_pos _
  have p1 : x ≤ x ^ ((11 : ℝ) / 2) := by simpa using mono (a := 1) (b := 11 / 2) (by norm_num)
  have yz : x ^ (eps / 10) ≤ x ^ (eps / 3) := mono (by linarith)
  have zL : 4 * x ^ (eps / 3) ≤ x ^ eps := by
    have e : x ^ eps = x ^ (2 * eps / 3) * x ^ (eps / 3) := by rw [← Real.rpow_add hx0]; congr 1; ring
    have : x ^ (eps / 10) ≤ x ^ (2 * eps / 3) := mono (by linarith)
    rw [e]; gcongr; linarith
  have hS : Real.sqrt (bx x eps) = Real.exp (x ^ eps / 2) := by
    unfold bx; rw [Real.exp_half]
  have hZ : 1 ≤ Real.exp (x ^ (eps / 3)) := Real.one_le_exp (by positivity)
  have ha : bx x eps ≤ aC x eps := le_mul_of_one_le_left hb.le (hx.trans p1)
  refine ⟨?_, ?_, ?_, div_le_self (hb.le.trans ha) hZ, ha, mul_le_mul_of_nonneg_right hp hb.le⟩
  · have := Real.add_one_le_exp (x ^ (eps / 10)); linarith
  · rw [hS, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  · rw [hS, bpC, aC, bx, le_div_iff₀ hx0, le_div_iff₀ (Real.exp_pos _), mul_right_comm, ← Real.exp_add, mul_comm]
    exact mul_le_mul p1 (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)

theorem exists_place (R : Ranks) (Del h : ℕ) (x a b b' S M : ℝ) (hD : 1 ≤ Del) (hh : R.t + 3 ≤ 2 * h) (hx : 1 ≤ x)
    (hS : S * S = b) (hM : 10 ≤ M) (hMS : M * M ≤ S) (hSb : S ≤ b' / x) (hba' : b' ≤ a) (hba : b ≤ a) (haM : a ≤ M * b)
    (hkD : 4 * (R.k : ℝ) * Del ≤ M) (heta : 2 * (R.m : ℝ) * h ≤ M) (p : Prop) :
    ∃ P : HCParam R, (∀ i, P.v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * Del)) ∧
      (∀ (l : ℕ) (hl : l < R.k - 2), P.u ⟨l + 1, by omega⟩ = P.v ⟨l, by omega⟩ - 1 / 2) ∧
      (∀ (j : ℕ) (hj : j + 1 < R.m), P.b ⟨j + 1, hj⟩ - P.b ⟨j, by omega⟩ = 2 * h) ∧
      (∀ j, S ≤ (P.b j : ℝ) ∧ (P.b j : ℝ) ≤ b ^ 2) ∧
      (∀ h0 h1, (P.b ⟨R.m - 1, h1⟩ : ℝ) ≤ 2 * (P.b ⟨0, h0⟩ : ℝ)) ∧
      (p → ∀ k0 k1 m0, ((P.u ⟨0, k0⟩ : ℝ) = (⌈a⌉ : ℝ) + ((R.k : ℝ) - 1) / 2 ∧
          (P.u ⟨R.k - 1, k1⟩ : ℝ) = -(⌈b'⌉ : ℝ) - ((R.k : ℝ) - 1) / 2 ∧
          (P.b ⟨0, m0⟩ : ℝ) = (⌈b'⌉ : ℝ) + (⌊b' / x⌋ : ℝ) ∧
          ∀ j, (P.e j : ℝ) ≤ (⌈b'⌉ : ℝ) + b' / x + 2 * (R.m : ℝ) * h) ∧
        S ≤ (P.u ⟨0, k0⟩ : ℝ) ∧ (P.u ⟨0, k0⟩ : ℝ) ≤ b ^ 2 ∧ 3 ≤ (P.b ⟨0, m0⟩ : ℝ) + (P.u ⟨R.k - 1, k1⟩ : ℝ) ∧
          (P.b ⟨0, m0⟩ : ℝ) / 2 ≤ -(P.u ⟨R.k - 1, k1⟩ : ℝ)) ∧
      (¬ p → (∀ k0, P.u ⟨0, k0⟩ = ((R.k - 2 : ℕ) : ℚ) * (4 * Del) + 4 * R.k * Del + 1 / 2) ∧
        (∀ k1, P.u ⟨R.k - 1, k1⟩ = -1 / 2) ∧ ∀ j, b ≤ (P.b j : ℝ) ∧ (P.e j : ℝ) ≤ b + 2 * (R.m : ℝ) * h + 1) := by
  obtain ⟨k', hk'⟩ := R.k_even
  have hk2 : (R.k : ℝ) = 2 * k' := by rw [hk']; push_cast; ring
  have hk3 : 3 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hk0 : (1 : ℝ) ≤ k' := by exact_mod_cast (by omega : 1 ≤ k')
  have hD' : (1 : ℝ) ≤ Del := by exact_mod_cast hD
  have hkM : (R.k : ℝ) ≤ M := by nlinarith
  have hM2 : 10 * M ≤ S := by nlinarith
  have hSb0 : 10 * S ≤ b := by nlinarith
  have hbb : 10 * (M * b) ≤ b ^ 2 := by nlinarith
  have hMb : 10 * b ≤ M * b := by nlinarith
  have hq : b' / x ≤ b' := div_le_self (by
    have h1 : 0 ≤ b' / x := by linarith
    have h2 : b' = b' / x * x := by field_simp
    rw [h2]; positivity) hx
  have c1 := Int.le_ceil a
  have c2 := Int.ceil_lt_add_one a
  have c3 := Int.le_ceil b
  have c4 := Int.ceil_lt_add_one b
  have c5 := Int.le_ceil b'
  have c6 := Int.ceil_lt_add_one b'
  have c7 := Int.floor_le (b' / x)
  have c8 := Int.lt_floor_add_one (b' / x)
  have hj : ∀ j : Fin R.m, 0 ≤ 2 * (h : ℝ) * (j.1 : ℝ) ∧ 2 * (h : ℝ) * (j.1 : ℝ) + h ≤ 2 * (R.m : ℝ) * h := fun j => by
    have : (j.1 : ℝ) + 1 ≤ R.m := by exact_mod_cast j.2
    have : (0 : ℝ) ≤ h := by positivity
    exact ⟨by positivity, by nlinarith⟩
  have hh0 : (0 : ℝ) ≤ h := by positivity
  have hk4 : ((R.k - 2 : ℕ) : ℝ) * (4 * Del) ≤ M := by
    have : ((R.k - 2 : ℕ) : ℝ) ≤ R.k := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  have common : ∀ (B : ℤ) (P : HCParam R), S ≤ B → (B : ℝ) + M ≤ b ^ 2 → (∀ j, P.b j = B + 2 * h * j.1) →
      (∀ (j : ℕ) (hj : j + 1 < R.m), P.b ⟨j + 1, hj⟩ - P.b ⟨j, by omega⟩ = 2 * h) ∧
      (∀ j, S ≤ (P.b j : ℝ) ∧ (P.b j : ℝ) ≤ b ^ 2) ∧
      (∀ h0 h1, (P.b ⟨R.m - 1, h1⟩ : ℝ) ≤ 2 * (P.b ⟨0, h0⟩ : ℝ)) := by
    intro B P B1 B2 hb
    refine ⟨fun j _ => by rw [hb, hb]; push_cast; ring, fun j => ?_, fun h0 h1 => ?_⟩
    · have := hj j
      rw [hb]; push_cast; constructor <;> linarith
    · have := hj ⟨R.m - 1, h1⟩
      rw [hb, hb]; push_cast at this ⊢; linarith
  by_cases hp : p
  · obtain ⟨P, hv, u0, u1, hl, hb, he⟩ := exists_hc R Del h (⌈a⌉ + k' - 1) (-⌈b'⌉ - k' + 1) (⌈b'⌉ + ⌊b' / x⌋) hD hh
      (by rw [← Int.cast_le (R := ℝ)]; push_cast; linarith)
      (by rw [← Int.cast_le (R := ℝ)]; push_cast; linarith)
      (by rw [← Int.cast_le (R := ℝ)]; push_cast; linarith)
    obtain ⟨d1, d2, d3⟩ := common _ P (by push_cast; linarith) (by push_cast; linarith) hb
    refine ⟨P, hv, hl, d1, d2, d3, fun _ k0 k1 m0 => ?_, fun h => absurd hp h⟩
    rw [u0, u1, hb]
    push_cast
    refine ⟨⟨by linarith, by linarith, by ring, fun j => ?_⟩, by linarith, by linarith, by linarith, by linarith⟩
    have := hj j
    rw [he]; push_cast; linarith
  · obtain ⟨P, hv, u0, u1, hl, hb, he⟩ := exists_hc R Del h (((R.k - 2 : ℕ) : ℤ) * (4 * Del) + 4 * R.k * Del) 0 ⌈b⌉ hD hh
      (le_add_of_nonneg_right (by positivity)) le_rfl
      (by rw [← Int.cast_le (R := ℝ)]; push_cast; linarith)
    obtain ⟨d1, d2, d3⟩ := common _ P (by linarith) (by linarith) hb
    refine ⟨P, hv, hl, d1, d2, d3, fun h => absurd h hp, fun _ => ⟨fun k0 => ?_, fun k1 => ?_, fun j => ?_⟩⟩
    · rw [u0]; push_cast; ring
    · rw [u1]; norm_num
    · have := hj j
      rw [hb, he]; push_cast; constructor <;> linarith

set_option maxHeartbeats 800000 in

theorem exists_record (eps CD CG : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hCD : 0 ≤ CD) (hCG : 0 < CG) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 1 < x ∧ ∃ (D : D7) (eta : ℝ), D.host.TT.Nonempty ∧ (∃ τ, Top D τ) ∧ (∃ τ, ¬ Top D τ) ∧
      Glob D x eps CD 9 1 ∧ OneScale D x eps eta ∧ Nodes D x eps ∧ Labels D x eps CG := by
  obtain ⟨x1, hb⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x2, hl⟩ := large eps (1000 + 9 * CD) h0 (by linarith)
  obtain ⟨x3, hN⟩ := rankNums_of_rankVal eps CD h0 h1 hCD
  obtain ⟨x4, hR⟩ := exists_ranks_cyclic_frame eps h0 h1
  obtain ⟨x5, hH⟩ := exists_host_level eps h0 h1
  refine ⟨max (max x1 x2) (max x3 (max x4 x5)), fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4, hx5⟩ := hx
  obtain ⟨h6, hlog, hK, hy, hpw, ab⟩ := hl x hx2
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  refine ⟨by linarith, ?_⟩
  obtain ⟨s, rfl, rfl⟩ : ∃ s : Scale, s.x = x ∧ s.eps = eps := ⟨⟨x, eps, by linarith, h0, h1, 1, le_rfl⟩, rfl, rfl⟩
  obtain ⟨R, hV, he, hφ⟩ := hR s rfl hx4
  obtain ⟨bf, bm, br, kr, -, bL, scaledRowVectorOperator, -, -, -, -, -, -, bt, bN, -, -⟩ := hb s R rfl hx1 hV
  obtain ⟨D1, D2, nums⟩ := hN s R rfl hx3 hV
  obtain ⟨H, T, π, Tp, Tl, Tne, pK, pn, pc, hg, ht, tt, t2, lw, ⟨-, sp⟩, rd, gw, T1, T2⟩ := hH s R rfl hx5 hV he hφ
  obtain ⟨G⟩ := GlobalTheory.MemLoc.localGap_nonempty H
  clear hb hl hN hR hH
  haveI : Fact T.Prime := ⟨Tp⟩
  unfold Scale.L at bL scaledRowVectorOperator
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hx1' h
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := weight_sizes s.x s.eps h0 hx1' hy (hpw _ (by linarith))
  obtain ⟨Del, hDel⟩ : ∃ Del, Del = delOf s.x s.eps CD R := ⟨_, rfl⟩
  rw [← hDel] at D1 D2 nums
  obtain ⟨h, h1', h2'⟩ : ∃ h : ℕ, s.x ^ (402 : ℝ) ≤ h ∧ (h : ℝ) ≤ 2 * s.x ^ (402 : ℝ) := by
    have := Nat.ceil_lt_add_one (a := s.x ^ (402 : ℝ)) (by positivity)
    have := Real.one_le_rpow hx1' (z := 402) (by norm_num)
    exact ⟨_, Nat.le_ceil _, by linarith⟩
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have bk : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast kr) br
  have hth : R.t + 3 ≤ 2 * h := by
    have a1 := ab 0 402 3 (by norm_num) (by linarith)
    have a2 : s.x ^ (401 : ℝ) ≤ s.x ^ (402 : ℝ) := mono (by norm_num)
    rw [Real.rpow_zero] at a1
    have : (R.t : ℝ) + 3 ≤ 2 * h := by linarith
    exact_mod_cast this
  have hkD : 4 * (R.k : ℝ) * Del ≤ Real.exp (s.x ^ (s.eps / 10)) := by
    have a1 := ab (5 + (9 * CD + 1)) (9 * CD + 7) 4 (by norm_num) (by linarith)
    rw [Real.rpow_add hx0, ← mul_assoc] at a1
    refine le_trans (le_trans ?_ a1) (hpw _ (by linarith))
    gcongr
  have hm0 : (0 : ℝ) < R.m := by exact_mod_cast (by omega : 0 < R.m)
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le (by positivity) h1'
  have heta : 2 * (R.m : ℝ) * h ≤ Real.exp (s.x ^ (s.eps / 10)) := by
    have a1 := ab (1 + 402) 404 4 (by norm_num) (by linarith)
    rw [Real.rpow_add hx0, Real.rpow_one] at a1
    have a2 : (R.m : ℝ) * h ≤ s.x * (2 * s.x ^ (402 : ℝ)) := by gcongr
    have a3 := hpw 404 (by linarith)
    linarith
  choose hc hv hlet hgb hw hbm htop hoff using fun τ : Tau2 R =>
    exists_place R Del h s.x _ _ _ _ _ D1 hth hx1' (Real.mul_self_sqrt (Real.exp_pos _).le) w1 w2 w3 w4 w5 w6 hkD heta
      (∃ t : H.TT, (τ : R.GG) = R.tau1 t)
  have hD0 : (0 : ℚ) < Del := by exact_mod_cast D1
  have hD1 : (1 : ℝ) ≤ Del := by exact_mod_cast D1
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
      (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * (Del : ℚ) := fun τ l hl => by
    rw [hv, hv]
    simp only
    rw [show R.k - 2 - l = (R.k - 2 - (l + 1)) + 1 by omega]
    push_cast; ring
  have hT0 : (0 : ℝ) < T := by exact_mod_cast Tp.pos
  have hf0 : (0 : ℝ) < R.f := by have := R.ord_pos; exact_mod_cast (show 0 < 2 * R.ord by omega)
  have hGam : 1 < Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.x ^ s.eps) := Real.one_lt_exp_iff.2 (by positivity)
  have hw2 : (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * T :=
    le_mul_of_one_le_left hT0.le (le_add_of_nonneg_right (by positivity))
  obtain ⟨r1, -⟩ := rd_bounds H
  obtain ⟨pl1, pl2⟩ := factPlaces R.toFrame
  refine ⟨rankRecord H hc Del hD0 hgap hlet (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 0 T T hT0 _ hGam
    le_rfl hw2 hg ht Tl Tne π pK pn pc G, 2 * (R.m : ℝ) * h, tt, ?_, ?_,
    ⟨?_, r1, gw, fun _ => ⟨T1, T2⟩, fun (τ : Tau2 R) j (hj : j + 1 < R.m) => ?_,
      fun (τ : Tau2 R) (i : Fin (R.k - 1)) => ?_, fun (τ : Tau2 R) hτ => ?_⟩,
    ⟨by positivity, ?_, fun τ hτ => (htop τ hτ _ _ _).1, fun τ hτ => (hoff τ hτ).2.2⟩,
    ⟨hw, fun τ => hbm τ _ _, fun τ hτ => (htop τ hτ _ _ _).2⟩,
    ⟨t2, ⟨⌈(405 : ℝ) * Real.log s.x⌉₊, ?_, ?_⟩, sp, hCG, fun _ => Real.log_exp _⟩⟩
  · obtain ⟨t, ht'⟩ := tt
    exact ⟨⟨R.tau1 t, (pl1 _).2 (Or.inl ⟨t, rfl⟩)⟩, ⟨t, ht'⟩, rfl⟩
  · exact ⟨⟨R.tau2 0, (pl1 _).2 (Or.inr ⟨0, rfl⟩)⟩, fun ⟨t, ht'⟩ => pl2 t.1 0 ht'.symm⟩
  · show RankNums s.x s.eps CD R.m R.f R.k (Real.log H.rdE) ((Del : ℚ) : ℝ)
    rw [Rat.cast_natCast]
    exact nums _ (Real.log_le_log two_pos r1) rd
  · show s.x ^ (s.eps / 100) * (R.r : ℝ) ^ 19 * (R.f : ℝ) ^ 5 * s.x ^ s.eps ≤
      (((hc τ).b ⟨j + 1, hj⟩ - (hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)
    rw [hgb]
    have a1 : (R.r : ℝ) ^ 19 ≤ s.x ^ ((5 : ℝ) * (19 : ℕ)) := by rw [Real.rpow_mul_natCast hx0.le]; gcongr
    have a2 : (R.f : ℝ) ^ 5 ≤ s.x ^ ((3 : ℝ) * (5 : ℕ)) := by rw [Real.rpow_mul_natCast hx0.le]; gcongr
    have a3 : s.x ^ (s.eps / 100 + 5 * (19 : ℕ) + 3 * (5 : ℕ) + s.eps) ≤ s.x ^ (402 : ℝ) := mono (by push_cast; linarith)
    rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_add hx0] at a3
    push_cast
    refine le_trans (le_trans ?_ a3) (by linarith)
    gcongr
  · show 0 ≤ (((hc τ).v i : ℚ) : ℝ) ∧ (((hc τ).v i : ℚ) : ℝ) ≤ 4 * (R.k : ℝ) * ((Del : ℚ) : ℝ)
    rw [hv]
    push_cast
    have : ((R.k - 2 - i.1 : ℕ) : ℝ) ≤ R.k := by exact_mod_cast (by omega : R.k - 2 - i.1 ≤ R.k)
    have a1 := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 4 * Del)
    exact ⟨by positivity, by linarith⟩
  · obtain ⟨o1, o2, -⟩ := hoff τ hτ
    show 4 * (R.k : ℝ) * ((Del : ℚ) : ℝ) ≤ (((hc τ).u ⟨0, by omega⟩ : ℚ) : ℝ) - (((hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) ∧
      (((hc τ).u ⟨0, by omega⟩ : ℚ) : ℝ) - (((hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) ≤ 8 * (R.k : ℝ) * ((Del : ℚ) : ℝ) ∧
      (((hc τ).u ⟨R.k - 1, by omega⟩ : ℚ) : ℝ) = (((hc τ).v ⟨R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2
    rw [o1, o2, hv, hv]
    simp only [Nat.sub_zero, Nat.sub_self]
    push_cast
    have a1 : (1 : ℝ) ≤ R.k * Del := one_le_mul_of_one_le_of_one_le hk1 hD1
    exact ⟨by linarith, by linarith, by norm_num⟩
  · rw [Real.log_le_iff_le_exp (by positivity)]
    exact heta.trans (Real.exp_le_exp.2 (mono (by linarith)))
  · show Real.logb 5 ((R.n : ℝ) * R.N R.m / R.m) ≤ _
    have hn0 : (0 : ℝ) < R.n := by exact_mod_cast (show 0 < R.n from R.ord_pos)
    have hN0 : (0 : ℝ) < R.N R.m := by
      have : 0 < R.N R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
    have a1 : (R.n : ℝ) * R.N R.m / R.m ≤ s.x ^ ((3 : ℝ) + 402) := by
      rw [Real.rpow_add hx0]
      refine (div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ R.m))).trans ?_
      gcongr
      linarith
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
    refine a1.trans ?_
    have a2 := Nat.le_ceil ((405 : ℝ) * Real.log s.x)
    have a3 : (1 : ℝ) ≤ Real.log 5 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos (by norm_num)]
    have a4 := mul_le_mul_of_nonneg_right a3 (Nat.cast_nonneg (α := ℝ) ⌈(405 : ℝ) * Real.log s.x⌉₊)
    exact Real.exp_le_exp.2 (by linarith)
  · show _ ≤ H.Lw
    rw [lw, Lwv]; omega

theorem inhabited_at_large_scale (eps CD CG : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hCD : 0 ≤ CD) (hCG : 0 < CG) :
    (∃ x0 : ℝ, ∀ x, x0 ≤ x → ∃ (m e k : ℕ) (lrd Del : ℝ), Even m ∧ Even k ∧
      RankNums x eps CD m ((2 * 2 ^ e : ℕ) : ℝ) k lrd Del) ∧
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 1 < x ∧ ∃ (D : D7) (eta : ℝ), D.host.TT.Nonempty ∧ (∃ τ, Top D τ) ∧ (∃ τ, ¬ Top D τ) ∧
      Glob D x eps CD 9 1 ∧ OneScale D x eps eta ∧ Nodes D x eps ∧ Labels D x eps CG := by
  refine ⟨?_, exists_record eps CD CG h0 h1 hCD hCG⟩
  obtain ⟨x0, h⟩ := exists_rankNums eps CD h0 h1 hCD
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨m, e, k, Del, a1, a2, a3, -⟩ := h x hx
  exact ⟨m, e, k, 1, Del, a1, a2, a3⟩

end GlobalTheory.Diag.PG.Inhab

end
