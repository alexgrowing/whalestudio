import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer

theorem le_absNorm_of_natPrime_mem {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
    {P : Ideal S} (hP : P ≠ ⊤) {p : ℕ} (hp : p.Prime) (h : (p : S) ∈ P) : p ≤ Ideal.absNorm P := by
  have h1 : Ideal.absNorm P ∣ Ideal.absNorm (Ideal.span {(p : S)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
  have h2 : Ideal.absNorm (Ideal.span {(p : S)}) = p ^ Module.finrank ℤ S := by
    rw [Ideal.absNorm_span_singleton]
    have : ((p : S)) = algebraMap ℤ S (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [h2] at h1
  obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow hp).1 h1
  rcases i with _ | i
  · simp only [pow_zero] at he
    exact absurd (Ideal.absNorm_eq_one_iff.1 he) hP
  · rw [he]; exact Nat.le_self_pow (by omega) p

theorem leastSplitAuxiliaryPrime_le_absNorm_chosenPlace {D : D7} {T : Type} {L : LevCh D T} (P : Places L) :
    q0 D ≤ Ideal.absNorm (P.w P.v0).asIdeal := by
  classical
  have hv : P.v0 ∈ insert P.v0 (S1 D) := Finset.mem_insert_self _ _
  have h1 := P.basePlace_over_qZero
  rw [← P.w_over P.v0 hv] at h1
  have h2 : ((q0 D : ℕ) : 𝓞 D.host.E) ∈ (P.w P.v0).asIdeal := by
    simpa using h1
  exact le_absNorm_of_natPrime_mem (P.w P.v0).isPrime.ne_top (leastSplitAuxiliaryPrimeThetaChain_spec D).1 h2

theorem leastSplitAuxiliaryPrime_pow_depth_le_absNorm_modulus {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) :
    q0 D ^ depth0 D sc.cDep sc.b ≤ Ideal.absNorm (P.modul sc) := by
  classical
  unfold Places.modul
  rw [map_prod]
  have hv0 : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
  have hd : P.depth sc P.v0 = depth0 D sc.cDep sc.b := by simp [Places.depth]
  calc q0 D ^ depth0 D sc.cDep sc.b ≤ Ideal.absNorm ((P.w P.v0).asIdeal ^ P.depth sc P.v0) := by
        rw [map_pow, hd]; exact Nat.pow_le_pow_left (leastSplitAuxiliaryPrime_le_absNorm_chosenPlace P) _
    _ ≤ ∏ v ∈ P.S0, Ideal.absNorm ((P.w v).asIdeal ^ P.depth sc v) :=
        Finset.single_le_prod' (f := fun v => Ideal.absNorm ((P.w v).asIdeal ^ P.depth sc v))
          (fun v _ => Nat.one_le_iff_ne_zero.2
            (Ideal.absNorm_eq_zero_iff.not.2 (pow_ne_zero _ (P.w v).ne_bot))) hv0

theorem mono_le {f n L : ℝ} (hf : 1 ≤ f) (hn : 1 ≤ n) (hL : 1 ≤ L) {a b c : ℕ} (ha : a ≤ 2) (hb : b ≤ 5)
    (hc : c ≤ 1) : f ^ a * n ^ b * L ^ c ≤ f ^ 2 * n ^ 5 * L := by
  have h1 : f ^ a ≤ f ^ 2 := pow_le_pow_right₀ hf ha
  have h2 : n ^ b ≤ n ^ 5 := pow_le_pow_right₀ hn hb
  have h3 : L ^ c ≤ L := by simpa using pow_le_pow_right₀ hL hc
  have p1 : 0 ≤ f ^ a := pow_nonneg (by linarith) _
  have p2 : 0 ≤ n ^ b := pow_nonneg (by linarith) _
  have p3 : 0 ≤ L ^ c := pow_nonneg (by linarith) _
  exact mul_le_mul (mul_le_mul h1 h2 p2 (p1.trans h1)) h3 p3 (mul_nonneg (p1.trans h1) (p2.trans h2))

theorem losses_le {C CF f n m L lY P lN : ℝ} (hC : 0 ≤ C) (hCF : 6510 ≤ CF) (hf : 1 ≤ f) (hn : C + 1 ≤ n)
    (hm0 : 0 ≤ m) (hmn : m ≤ n) (hL : 1 ≤ L) (hlY : lY ≤ n ^ 3 + 21 * L)
    (hP : CF * f ^ 2 * n ^ 6 * L ≤ P) (hN : P < lN) :
    Real.log 2 + (C * f * n ^ 4 * L + (6 * n + 9) * f) +
      f * (Real.log 2 + m * (Real.log 2 + C * f * n ^ 4 * L + lY)) ≤ lN / 2 := by
  have hn1 : 1 ≤ n := by linarith
  have hl2 : Real.log 2 ≤ 1 := (Real.log_two_lt_d9.trans (by norm_num)).le
  have hf0 : 0 ≤ f := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hfm : 0 ≤ f * m := mul_nonneg hf0 hm0
  have hfmn : f * m ≤ f * n := mul_le_mul_of_nonneg_left hmn hf0
  have k1 : (1 : ℝ) ≤ f ^ 2 * n ^ 5 * L := by simpa using mono_le hf hn1 hL (a := 0) (b := 0) (c := 0) (by norm_num) (by norm_num) (by norm_num)
  have k2 : f * n ^ 4 * L ≤ f ^ 2 * n ^ 5 * L := by simpa using mono_le hf hn1 hL (a := 1) (b := 4) (c := 1) (by norm_num) (by norm_num) (by norm_num)
  have k3 : f * n ≤ f ^ 2 * n ^ 5 * L := by simpa using mono_le hf hn1 hL (a := 1) (b := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num)
  have k4 : f ≤ f ^ 2 * n ^ 5 * L := by simpa using mono_le hf hn1 hL (a := 1) (b := 0) (c := 0) (by norm_num) (by norm_num) (by norm_num)
  have k5 : f * n ^ 4 ≤ f ^ 2 * n ^ 5 * L := by simpa using mono_le hf hn1 hL (a := 1) (b := 4) (c := 0) (by norm_num) (by norm_num) (by norm_num)
  have k6 : f * n * L ≤ f ^ 2 * n ^ 5 * L := by simpa using mono_le hf hn1 hL (a := 1) (b := 1) (c := 1) (by norm_num) (by norm_num) (by norm_num)
  have q0 : 0 ≤ C * f * n ^ 4 * L := by positivity
  have X0 : 0 ≤ 1 + C * f * n ^ 4 * L + (n ^ 3 + 21 * L) := by positivity
  have s1 : f * m * (Real.log 2 + C * f * n ^ 4 * L + lY) ≤ f * m * (1 + C * f * n ^ 4 * L + (n ^ 3 + 21 * L)) :=
    mul_le_mul_of_nonneg_left (by linarith) hfm
  have s2 : f * m * (1 + C * f * n ^ 4 * L + (n ^ 3 + 21 * L)) ≤ f * n * (1 + C * f * n ^ 4 * L + (n ^ 3 + 21 * L)) :=
    mul_le_mul_of_nonneg_right hfmn X0
  have s3 : f * n * (1 + C * f * n ^ 4 * L + (n ^ 3 + 21 * L)) =
      f * n + C * (f ^ 2 * n ^ 5 * L) + f * n ^ 4 + 21 * (f * n * L) := by ring
  have s4 : f * (Real.log 2 + m * (Real.log 2 + C * f * n ^ 4 * L + lY)) =
      f * Real.log 2 + f * m * (Real.log 2 + C * f * n ^ 4 * L + lY) := by ring
  have s5 : f * Real.log 2 ≤ f := by simpa using mul_le_mul_of_nonneg_left hl2 hf0
  have s6 : f * m * Real.log 2 ≤ f * n := by
    have := mul_le_mul_of_nonneg_left hl2 hfm
    linarith
  have s7 : (6 * n + 9) * f ≤ 15 * (f * n) := by nlinarith
  have hCK : C * (f * n ^ 4 * L) ≤ C * (f ^ 2 * n ^ 5 * L) := mul_le_mul_of_nonneg_left k2 hC
  have hK0 : 0 ≤ f ^ 2 * n ^ 5 * L := by positivity
  have h42 : 2 * C + 42 ≤ 3255 * n := by linarith
  have hfin : (2 * C + 42) * (f ^ 2 * n ^ 5 * L) ≤ 3255 * n * (f ^ 2 * n ^ 5 * L) :=
    mul_le_mul_of_nonneg_right h42 hK0
  have hnK : 3255 * n * (f ^ 2 * n ^ 5 * L) = 3255 * (f ^ 2 * n ^ 6 * L) := by ring
  have hCF2 : 3255 * (f ^ 2 * n ^ 6 * L) ≤ CF / 2 * (f ^ 2 * n ^ 6 * L) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hP2 : CF / 2 * (f ^ 2 * n ^ 6 * L) = CF * f ^ 2 * n ^ 6 * L / 2 := by ring
  have hCfL : C * f * n ^ 4 * L = C * (f * n ^ 4 * L) := by ring
  rw [s4]
  nlinarith

theorem pays_of_log {Q Y n N : ℝ} {fN mN : ℕ} (hQ : 0 ≤ Q) (hY : 1 ≤ Y) (hn : 0 ≤ n) (hm : mN ≠ 0) (hN : 0 < N)
    (hmain : Real.log 2 + (Q + (6 * n + 9) * fN) + fN * (Real.log 2 + mN * (Real.log 2 + Q + Real.log Y)) ≤
      Real.log N / 2) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ Real.exp Q * (Y * (2 * s) ^ ((1 : ℝ) / mN)) ≤ 1 / 2 ∧
      2 * Real.exp (Q + (6 * n + 9) * fN) ≤ s ^ fN * Real.sqrt N ∧ 1 < s ^ fN * Real.sqrt N := by
  have hE : 1 ≤ Real.exp Q := Real.one_le_exp hQ
  set X := 2 * Real.exp Q * Y with hXdef
  have hX : 2 ≤ X := by nlinarith
  have hX0 : 0 < X := by linarith
  have hXm : 1 ≤ X ^ mN := one_le_pow₀ (by linarith)
  have hlX : Real.log X = Real.log 2 + Q + Real.log Y := by
    rw [hXdef, Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (Real.exp_pos Q).ne',
      Real.log_exp]
  have hs0 : 0 < (X ^ mN)⁻¹ / 2 := by positivity
  have hls : Real.log ((X ^ mN)⁻¹ / 2) = -(mN * Real.log X) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_inv, Real.log_pow]
  have hA : 2 * Real.exp (Q + (6 * n + 9) * fN) ≤ ((X ^ mN)⁻¹ / 2) ^ fN * Real.sqrt N := by
    have h1 : 0 < 2 * Real.exp (Q + (6 * n + 9) * fN) := by positivity
    have h2 : 0 < ((X ^ mN)⁻¹ / 2) ^ fN * Real.sqrt N := mul_pos (pow_pos hs0 _) (Real.sqrt_pos.2 hN)
    rw [← Real.log_le_log_iff h1 h2, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (pow_pos hs0 _).ne' (Real.sqrt_pos.2 hN).ne', Real.log_pow, Real.log_sqrt hN.le, hls, hlX]
    nlinarith
  refine ⟨(X ^ mN)⁻¹ / 2, hs0, ?_, ?_, hA, ?_⟩
  · have : (X ^ mN)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hXm
    linarith
  · have e1 : 2 * ((X ^ mN)⁻¹ / 2) = (X ^ mN)⁻¹ := by ring
    rw [e1, Real.inv_rpow (by positivity), one_div, Real.pow_rpow_inv_natCast hX0.le hm, hXdef]
    apply le_of_eq
    field_simp
  · have : 1 ≤ Real.exp (Q + (6 * n + 9) * fN) := Real.one_le_exp (by positivity)
    linarith

end GlobalTheory.SepPer

namespace GlobalTheory.SepPer

theorem depth_pays : DepthPays := by
  intro C hC ε CF hCF
  refine ⟨C + 1, fun D large₂ _ hx hS T L μ0 _ G W M _ => ?_⟩
  show Pays D (loss D C large₂.sc.b) (Ideal.absNorm G.modul)
  obtain ⟨-, -, -, hm44, hk, hb, -, hg, -, hrd1, hrd2, -, -, -⟩ := hS

  have hfR : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  have hfk : D.R.f ≤ D.R.k := by unfold Ranks.f Ranks.n; exact D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by unfold Ranks.f Ranks.n; exact D.R.m_le_f
  have hrk : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.two_le_m; unfold Ranks.r; omega
  have hf1 : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hfn : (D.R.f : ℝ) ≤ (D.R.r : ℝ) + 1 := by
    have : D.R.f ≤ D.R.r + 1 := by omega
    exact_mod_cast this
  have hmn : (D.R.m : ℝ) ≤ (D.R.r : ℝ) + 1 := by
    have : D.R.m ≤ D.R.r + 1 := by omega
    exact_mod_cast this
  have hkn : (D.R.k : ℝ) ≤ (D.R.r : ℝ) + 1 := by
    have : D.R.k ≤ D.R.r + 1 := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by omega
    exact_mod_cast this
  have hf1' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hm44' : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44

  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hL : 1 ≤ large₂.sc.L := by
    have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
    have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    have h1 : 1 ≤ D.R.f * D.R.N D.R.m ^ 2 * D.host.d :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 44 ≤ D.R.m * (D.R.f * D.R.N D.R.m ^ 2 * D.host.d) :=
      hm44.trans (Nat.le_mul_of_pos_right _ h1)
    have h3 : (44 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : ((D.R.m * (D.R.f * D.R.N D.R.m ^ 2 * D.host.d) : ℕ) : ℝ) =
          (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by push_cast; ring
      rw [← this]; exact_mod_cast h2
    have h4 : Real.exp 1 < Real.exp large₂.sc.L := by
      have h5 := Real.exp_one_lt_d9
      have e : Real.exp large₂.sc.L = large₂.sc.b := rfl
      rw [e]; linarith only [h5, h3, hb]
    exact (Real.exp_lt_exp.1 h4).le

  have hrd2' : (2 : ℝ) ≤ D.host.rdE := Formalism.MainNotions.flipTwoThree.two_le_rdE D.host
  have hlrd : 1 / 2 ≤ Real.log D.host.rdE := by
    have h1 := Real.log_le_log (by norm_num) hrd2'
    have h2 := Real.log_two_gt_d9
    linarith only [h1, h2]

  have hkC : C + 1 ≤ (D.R.k : ℝ) := by
    have a1 : (44 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := hm44'.trans (le_self_pow₀ (by linarith) (by norm_num))
    have a2 : 1 ≤ (D.R.m : ℝ) ^ 3 * large₂.sc.L * Real.log D.host.rdE := by
      have b1 : (D.R.m : ℝ) ^ 3 * large₂.sc.L ≥ 44 := by nlinarith only [a1, hL]
      nlinarith only [b1, hlrd]
    have hx1 : C + 1 ≤ large₂.sc.x := hx
    have hx2 : large₂.sc.x ≤ large₂.sc.x ^ 2 := by nlinarith only [hx1, hC]
    have a3 : large₂.sc.x ^ 2 * 1 ≤ large₂.sc.x ^ 2 * ((D.R.m : ℝ) ^ 3 * large₂.sc.L * Real.log D.host.rdE) :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    have e : large₂.sc.x ^ 2 * ((D.R.m : ℝ) ^ 3 * large₂.sc.L * Real.log D.host.rdE) =
        large₂.sc.x ^ 2 * (D.R.m : ℝ) ^ 3 * large₂.sc.L * Real.log D.host.rdE := by ring
    linarith only [hx1, hx2, a3, e, hk]

  have hNat := leastSplitAuxiliaryPrime_pow_depth_le_absNorm_modulus G.pl (⟨1, CF, large₂.sc.b⟩ : Consts)
  have hq1 : (1 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.one_lt
  have hNq : ((q0 D : ℝ)) ^ depth0 D CF large₂.sc.b ≤ (Ideal.absNorm G.modul : ℝ) := by exact_mod_cast hNat
  have hN0 : 0 < (Ideal.absNorm G.modul : ℝ) := lt_of_lt_of_le (pow_pos (by linarith) _) hNq
  have hlogN : sizeP D CF large₂.sc.b < Real.log (Ideal.absNorm G.modul : ℝ) := by
    have h1 := Real.log_le_log (pow_pos (by linarith) _) hNq
    rw [Real.log_pow] at h1
    linarith only [h1, sizeP_lt D CF large₂.sc.b]

  have hP : CF * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + 1) ^ 6 * large₂.sc.L ≤ sizeP D CF large₂.sc.b := by
    unfold sizeP nRk
    push_cast
    have hZ : 1 ≤ ((D.R.r : ℝ) + 1) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) * (D.host.pde' : ℝ) *
        |(discr D.host.E : ℝ)| := by
      have g0 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_lt.le
      have g1 : (1 : ℝ) ≤ D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).one_lt.le
      have p0 : (1 : ℝ) ≤ D.host.pde := by exact_mod_cast D.host.pde_prime.one_lt.le
      have p1 : (1 : ℝ) ≤ D.host.pde' := by exact_mod_cast D.host.pde'_prime.one_lt.le
      have dd : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
        have h : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs (discr_ne_zero _)
        rw [← Int.cast_abs]; exact_mod_cast h
      have n1 : (1 : ℝ) ≤ (D.R.r : ℝ) + 1 := by linarith
      have := one_le_mul_of_one_le_of_one_le n1 g0
      have := one_le_mul_of_one_le_of_one_le this g1
      have := one_le_mul_of_one_le_of_one_le this p0
      have := one_le_mul_of_one_le_of_one_le this p1
      exact one_le_mul_of_one_le_of_one_le this dd
    have hle : large₂.sc.b ≤ large₂.sc.b * ((D.R.r : ℝ) + 1) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |(discr D.host.E : ℝ)| := by
      have h6 := mul_le_mul_of_nonneg_left hZ hb0.le
      have e : large₂.sc.b * (((D.R.r : ℝ) + 1) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) * (D.host.pde' : ℝ) *
        |(discr D.host.E : ℝ)|) = large₂.sc.b * ((D.R.r : ℝ) + 1) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |(discr D.host.E : ℝ)| := by ring
      linarith only [h6, e]
    have hlog := Real.log_le_log hb0 hle
    rw [hlogb] at hlog
    have hpos : 0 ≤ CF * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + 1) ^ 6 := by positivity
    exact mul_le_mul_of_nonneg_left hlog hpos

  have hG : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ 20 * large₂.sc.L := by
    push_cast
    rw [Real.log_mul (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)]
    linarith only [hg 0, hg 1, hL]
  have hY1 : 1 ≤ (D.R.r : ℝ) ^ 2 * (D.R.f : ℝ) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr1) hf1'
  have hG1 : (1 : ℝ) ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by
    have : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.one_le_iff_ne_zero.2
      (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    exact_mod_cast this
  have hrdisc : rdisc D = D.host.rdE := rfl
  have hlY : Real.log ((D.R.r : ℝ) ^ 2 * (D.R.f : ℝ) * ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) * rdisc D) ≤
      ((D.R.r : ℝ) + 1) ^ 3 + 21 * large₂.sc.L := by
    rw [hrdisc, Real.log_mul (by positivity) (ne_of_gt (by linarith only [hrd2'])), Real.log_mul (by positivity) (ne_of_gt (by linarith only [hG1]))]
    have h1 : Real.log ((D.R.r : ℝ) ^ 2 * (D.R.f : ℝ)) ≤ ((D.R.r : ℝ) + 1) ^ 3 := by
      have := Real.log_le_sub_one_of_pos (x := (D.R.r : ℝ) ^ 2 * (D.R.f : ℝ)) (by positivity)
      have h2 : (D.R.r : ℝ) ^ 2 * (D.R.f : ℝ) ≤ ((D.R.r : ℝ) + 1) ^ 2 * ((D.R.r : ℝ) + 1) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith only) 2) hfn (by positivity) (by positivity)
      have e : ((D.R.r : ℝ) + 1) ^ 2 * ((D.R.r : ℝ) + 1) = ((D.R.r : ℝ) + 1) ^ 3 := by ring
      linarith only [this, h2, e]
    have h3 : Real.log D.host.rdE ≤ large₂.sc.L := by linarith only [hrd1, hrd2, hL]
    linarith only [h1, h3, hG]

  unfold Pays loss
  rw [hfR, hlogb]
  apply pays_of_log (by positivity) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hY1 hG1) (by rw [hrdisc]; linarith only [hrd2'])) (by positivity) (by omega) hN0
  exact losses_le hC hCF hf1' (hkC.trans hkn) (by positivity) hmn hL hlY hP hlogN

end GlobalTheory.SepPer
