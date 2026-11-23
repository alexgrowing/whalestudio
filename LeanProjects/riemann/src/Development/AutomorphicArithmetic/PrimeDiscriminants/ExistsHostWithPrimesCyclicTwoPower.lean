import Mathlib
import Development.AutomorphicArithmetic.MeanSquareBounds.pairEx
import Development.AutomorphicArithmetic.CharacterBoxes.PairHyp
import Development.AutomorphicArithmetic.ShortNorms.typePrimesN
import Development.AutomorphicArithmetic.ShortNorms.levelPrimeN
import Development.AutomorphicArithmetic.ShortNorms.MulLogLeRpowEventually
import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHost
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd

noncomputable section

namespace UpperTheory.Host

open Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits GlobalTheory.EX NumberField

theorem cyclic_two_power_frame_facts {R : Ranks} (hφ : R.toFrame = Formalism.HC.cyclicFrame R.e) :
    Function.Injective R.h ∧ R.o = 1 ∧ R.n = 2 ^ R.e := by
  have h : ∀ φ : Formalism.HC.Frame, ∀ e, φ = Formalism.HC.cyclicFrame e → Function.Injective φ.h ∧ φ.o = 1 ∧ φ.ord = 2 ^ e := by
    rintro _ e rfl
    exact ⟨Formalism.HC.frameCyc_h_injective e 1, Formalism.HC.cyclicFrame_index e, rfl⟩
  exact h _ _ hφ

def relevel {R : Ranks} (D : Host R) (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (h61 : ∀ i, 61 < g i)
    (T Lw : ℕ) (hL : 2 ≤ Lw) (hS : ∀ p ∈ ({g 0, g 1, 31, 61, T} : Finset ℕ), Nat.Coprime p D.QS) : Host R :=
  { withTop D with
    levelPrimes := {g 0, g 1, 31, 61, T}
    g := g
    g_prime := hg
    g_ne := hne
    g_level := by intro i; fin_cases i <;> simp
    pde := 31
    pde' := 61
    pde_prime := by norm_num
    pde'_prime := by norm_num
    pde_ne := by norm_num
    pde_level := by simp
    pde_mod := by norm_num
    pde_ne_g := fun i => by have := h61 i; omega
    ccK_coprime := fun p _ => by rw [withTop_ccK, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := hS
    TT := Finset.univ
    T2 := {0}
    Lw := Lw
    two_le_Lw := hL
    second_set_range := fun s hs => by rw [Finset.mem_singleton.1 hs, mul_zero]; exact R.n0_pos
    second_set_no_relation := fun s₁ h₁ s₂ h₂ _ _ h12 =>
      absurd ((Finset.mem_singleton.1 h₁).trans (Finset.mem_singleton.1 h₂).symm) h12 }

theorem exists_host_with_primes_cyclic_two_power (R : Ranks) (hφ : R.toFrame = Formalism.HC.cyclicFrame R.e) (he : 2 ≤ R.e) {q d : ℕ}
    (hyp : HostHyp q d) (hbig : 4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) (h3 : q ≠ 3) (B : ℕ)
    (hsp : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ B → jacobiSym (-(d : ℤ)) p = 1) (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime)
    (hne : g 0 ≠ g 1) (h61 : ∀ i, 61 < g i) (T Lw : ℕ) (hL : 2 ≤ Lw) (hT : Odd T) :
    ∃ H : Host R, H.q = q ∧ H.d = d ∧ H.QS = 2 ^ (R.e + 2) ∧ H.splitBound = B ∧ H.g = g ∧ H.pde = 31 ∧ H.pde' = 61 ∧
      H.levelPrimes = {g 0, g 1, 31, 61, T} ∧ H.ccK = ⊤ ∧ H.TT = Finset.univ ∧ H.T2 = {0} ∧ H.Lw = Lw := by
  obtain ⟨hinj, ho, -⟩ := cyclic_two_power_frame_facts hφ
  obtain ⟨H0, eq, ed, hQS, h2G, h15, hMu, hPS, hEx, hs⟩ := Formalism.HC.exists_hostAx R.toFrame hinj he hyp
  have hF : HostParam.Seam.FieldRows H0.toHostRaw B :=
    ⟨hPS, hs, hEx, by rw [hQS]; exact Formalism.HC.D7.qs_le R.toFrame hinj he,
      by rw [ho, one_pow]; exact Nat.one_le_two_pow, eq ▸ h3, ed ▸ hsp, fun l hl h2 hd => by
        rw [hQS] at hd
        exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow hd)) h2⟩
  obtain ⟨c⟩ := HostParam.Seam.nonempty_choices H0.toHostRaw
  obtain ⟨D, hD, hB, -⟩ := UpperTheory.Top.admissible_ranks_of_CMDatum R H0 B c hF (by rw [eq, ed]; exact hbig)
  have hS : ∀ p ∈ ({g 0, g 1, 31, 61, T} : Finset ℕ), Nat.Coprime p D.QS := fun p hp => by
    have hq : D.QS = 2 ^ (R.e + 2) := by
      show D.toHostAx.QS = _
      rw [hD, hQS]
    have hgo : ∀ i, Odd (g i) := fun i => (hg i).odd_of_ne_two (by have := h61 i; omega)
    rw [hq]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_two_right]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [hgo 0, hgo 1, by decide, by decide, hT]
  refine ⟨relevel D g hg hne h61 T Lw hL hS, ?_, ?_, ?_, hB, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show D.toHostAx.q = q
    rw [hD, eq]
  · show D.toHostAx.d = d
    rw [hD, ed]
  · show D.toHostAx.QS = _
    rw [hD, hQS]

theorem exists_host_with_level_prime (eps c : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hc : 1 / 2 ≤ c) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → 2 ≤ R.e →
      R.toFrame = Formalism.HC.cyclicFrame R.e →
      ∃ (H : Host R) (T : ℕ) (π : 𝓞 H.E), T.Prime ∧ T ∈ H.levelPrimes ∧ (T ≠ H.pde ∧ T ≠ H.pde') ∧ (π : H.E) ∈ H.K ∧
        (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
        (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)} ∧
        (∀ i, H.g i % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧
        H.TT = Finset.univ ∧ H.T2 = {0} ∧ H.ccK = ⊤ ∧ H.Lw = Lwv s ∧ H.splitBound = ⌊s.x ^ (eps / 5)⌋₊ ∧
        H.QS = 2 ^ (R.e + 2) ∧ UpperTheory.Top.WinPair eps s.x H.q H.d ∧
        Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 3 * s.x ^ (eps / 5) * Real.log s.x ^ 2 ∧
        (∀ i, ((R.k : ℝ) * s.b) ^ 8 ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧ (H.g i : ℝ) ≤ s.b ^ 9) ∧
        s.b ^ (c * (R.m : ℝ)) ≤ (T : ℝ) ∧ (T : ℝ) ≤ s.b ^ (2 * c * (R.m : ℝ)) := by
  have hS : UpperTheory.T3.ShortNorm := GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound
  obtain ⟨x1, hb⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x2, hP⟩ := QH.pairEx 1 one_pos eps 1 h0 h1 le_rfl
  obtain ⟨x3, hQ⟩ := UpperTheory.T3.qdBig eps 1 h0 h1
  obtain ⟨x4, hG⟩ := UpperTheory.T3.typePrimesN hS eps h0
  obtain ⟨x5, hT⟩ := UpperTheory.T3.levelPrimeN hS eps h0 h1 c 9 (by linarith) (by norm_num)
  obtain ⟨x6, hl⟩ := Filter.eventually_atTop.1 (((isLittleO_log_rpow_atTop h0).bound (c := 1 / 41) (by norm_num)).and
    (Real.tendsto_log_atTop.eventually_ge_atTop 4))
  refine ⟨max (max x1 x2) (max (max x3 x4) (max x5 (max x6 8))), fun s R hs hx hR he hφ => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩, hx5, hx6, hx8⟩ := hx
  subst hs
  obtain ⟨bf, -, br, kr, -, -, scaledRowVectorOperator, -, -, -, -, -, -, -, -, ml, -⟩ := hb s R rfl hx1 hR
  obtain ⟨l1, l4⟩ := hl s.x hx6
  have hx0 : 0 < s.x := by linarith
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le (by linarith) h
  rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity)] at l1
  obtain ⟨q, d, hqd, -⟩ := hP s.x hx2
  obtain ⟨hyp, hsp, -⟩ := UpperTheory.Top.pairHyp _ _ _ _ hqd
  obtain ⟨hbig, d100⟩ := hQ { s with J := 1, one_le_J := le_rfl } R s.x q d rfl hx3 hR le_rfl (pairWin_self _) hqd
  obtain ⟨-, -, hn⟩ := cyclic_two_power_frame_facts hφ
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hyp.1.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hyp.2.1.pos
  have hz : 1 ≤ s.x ^ (s.eps / 5) := Real.one_le_rpow (by linarith) (by linarith)
  have hlog : Real.log (((2 ^ (R.e + 2) : ℕ) : ℝ) * q * d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    have a1 : ((2 ^ (R.e + 2) : ℕ) : ℝ) ≤ s.x ^ (4 : ℝ) := by
      have b1 : ((2 ^ (R.e + 2) : ℕ) : ℝ) = 2 * R.f := by
        rw [show R.f = 2 * R.n from rfl, hn]; push_cast; ring
      rw [b1, show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add hx0, Real.rpow_one]
      gcongr; linarith
    have a2 := Real.log_le_log (by positivity) a1
    rw [Real.log_rpow hx0] at a2
    rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul (by positivity) hq0.ne']
    have a3 : 4 * Real.log s.x ≤ Real.log s.x ^ 2 := by nlinarith
    have a4 : Real.log s.x ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := le_mul_of_one_le_left (by positivity) hz
    have a5 : s.x ^ (s.eps / 5) ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := le_mul_of_one_le_right (by positivity) (by linarith)
    linarith [hqd.q_up, hqd.d_up]
  have hd16 := hqd.d_mod
  have hN0 : 0 < 2 ^ (R.e + 2) * q * d := by have := hyp.1.pos; positivity
  have hM : UpperTheory.T3.ModAt s.x s.eps (2 ^ (R.e + 2) * q * d) d :=
    ⟨hyp.2.1, by omega, d100, hN0, Dvd.intro_left _ rfl, by simpa using hlog⟩
  obtain ⟨g, hg, hne, hdis⟩ := hG s.x hx4 _ d R.k R.r hM (by omega) (by omega) br
  have hbb : Real.exp (s.x ^ s.eps) = s.b := rfl
  rw [hbb] at hg
  have hb2 : 2 ≤ s.b := by have := Real.add_one_le_exp s.L; unfold Scale.b; linarith
  have hb0 : 0 < s.b := by linarith
  have bk : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast kr) br
  have k1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have g9 : ∀ i, (g i : ℝ) ≤ s.b ^ 9 := fun i => by
    have a1 : (R.k : ℝ) ^ 8 ≤ s.x ^ ((5 : ℝ) * (8 : ℕ)) := by rw [Real.rpow_mul_natCast hx0.le]; gcongr
    have a2 : 2 * s.x ^ ((5 : ℝ) * (8 : ℕ)) ≤ s.x ^ (41 : ℝ) := by
      rw [show (41 : ℝ) = 1 + 5 * (8 : ℕ) by norm_num, Real.rpow_add hx0, Real.rpow_one]
      gcongr; linarith
    have a3 : s.x ^ (41 : ℝ) ≤ s.b := by
      rw [Real.rpow_def_of_pos hx0, ← hbb]; exact Real.exp_le_exp.2 (by linarith)
    have a5 : 2 * (R.k : ℝ) ^ 8 ≤ s.b := by linarith
    calc (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 := (hg i).2.2.1
      _ = 2 * (R.k : ℝ) ^ 8 * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := by gcongr
      _ = s.b ^ 9 := by ring
  have h61 : ∀ i, 61 < g i := fun i => by
    have a1 : (1 * 2 : ℝ) ^ 8 ≤ ((R.k : ℝ) * s.b) ^ 8 := by gcongr
    have a2 : (61 : ℝ) < g i := by linarith [(hg i).2.1]
    exact_mod_cast a2
  have lg : ∀ i, Real.log (g i) ≤ 9 * s.x ^ s.eps := fun i => by
    refine (Real.log_le_log (by exact_mod_cast (hg i).1.pos) (g9 i)).trans (le_of_eq ?_)
    rw [Real.log_pow, ← hbb, Real.log_exp]; norm_num
  have f1 : (1 : ℝ) ≤ R.f := by
    have : 1 ≤ R.f := by rw [show R.f = 2 * R.n from rfl, hn]; have := Nat.two_pow_pos R.e; omega
    exact_mod_cast this
  have hV : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le f1 k1
  obtain ⟨T, Tp, T1, T2, Tn⟩ := hT s.x hx5 _ d (g 0) (g 1) R.m hM (hg 0).1.one_le (hg 1).1.one_le (lg 0) (lg 1)
    ((mono (by linarith)).trans ml) 1 (s.b ^ (c * (R.m : ℝ))) le_rfl (Real.one_le_rpow (by linarith) (by norm_num))
    (by positivity) (by rw [Real.log_rpow hb0, ← hbb, Real.log_exp])
  have m2 : (2 : ℝ) ≤ R.m := by exact_mod_cast hm
  have hbT : s.b ≤ s.b ^ (c * (R.m : ℝ)) := by
    conv_lhs => rw [← Real.rpow_one s.b]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  have T61 : 61 < T := by
    have a1 := Real.add_one_le_exp (s.x ^ s.eps)
    have a2 : (61 : ℝ) < T := by linarith
    exact_mod_cast a2
  have h3 : q ≠ 3 := by
    have h2 := R.rank_add_five_le
    have : 1 * 1 ≤ R.t * R.r := Nat.mul_le_mul (by omega) (by omega)
    have := hbig.1
    rw [mul_assoc] at this
    omega
  obtain ⟨H, rfl, rfl, e3, e4, rfl, e6, e7, e8, e9, e10, e11, e12⟩ := exists_host_with_primes_cyclic_two_power R hφ he hyp hbig h3
    ⌊s.x ^ (s.eps / 5)⌋₊ (fun p hp h2 hle => hsp p hp h2 ((Nat.le_floor_iff (by positivity)).1 hle)) g (fun i => (hg i).1)
    hne h61 T (Lwv s) (by unfold Lwv; omega) (Tp.odd_of_ne_two (by omega))
  rw [← e3] at hlog hg Tn hN0
  obtain ⟨π, pK, pn, pc⟩ := (GlobalTheory.Mem.An.normOne_iff_host R H _ T).1 Tn
  refine ⟨H, T, π, Tp, by rw [e8]; simp, ⟨by omega, by omega⟩, pK, pn, pc, fun i => ?_, hdis, e10, e11, e9, e12, e4, e3, hqd,
    hlog, fun i => ⟨(hg i).2.1, (hg i).2.2.1, g9 i⟩, T1.le, ?_⟩
  · have a := (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd H.d _ _ (by omega) (hg i).2.2.2).1
    exact (show _ % _ = 1 % _ from a).trans (Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega : 1 < H.d) (Nat.le_of_dvd hN0 (Dvd.intro_left _ rfl))))
  · rw [show 2 * c * (R.m : ℝ) = c * R.m + c * R.m by ring, Real.rpow_add hb0]
    refine T2.trans ?_
    gcongr
    linarith

end UpperTheory.Host

end
