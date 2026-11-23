import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadCharsCountOfDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GChiApproximationSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPrimesResidueGeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicativeWeightPrimeSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfEqOnCoprime
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.ChoiceOfModulus

theorem level_mem_bad {Q : ℝ} {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hN : (N : ℝ) ≤ Q) (hp : χ.IsPrimitive) (h2 : χ ^ 2 = 1) (hr : GlobalTheoryTheory.IsRealChar χ)
    (h1 : χ ≠ 1) (hb : ¬ GlobalTheoryTheory.GoodFor Q χ) :
    N ∈ (fun c : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) => c.1 + 1) ''
      Formalism.HermitianLattices.GL2PrimeSums.BadChars Q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  refine ⟨⟨n, χ⟩, ⟨hN, hp, h2, fun hg => hb ⟨hp, hr, hN, fun s hs ht h0 => ?_⟩⟩, rfl⟩
  exact hg s hs ht ⟨Or.inl h1, h0⟩

theorem card_le_of_levels {Q B : ℝ} (hB0 : 0 ≤ B)
    (hB : (((Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal B)
    (S : Finset ℕ) (g : ℕ → ℕ) (hg : Function.Injective g)
    (h : ∀ q ∈ S, g q ∈ (fun c : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) => c.1 + 1) ''
      Formalism.HermitianLattices.GL2PrimeSums.BadChars Q) : (S.card : ℝ) ≤ B := by
  have h1 : ((S.image g : Finset ℕ) : Set ℕ) ⊆
      (fun c : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) => c.1 + 1) ''
      Formalism.HermitianLattices.GL2PrimeSums.BadChars Q := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hn)
    exact h q hq
  have h2 := (Set.encard_le_encard h1).trans (Set.encard_image_le _ _)
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hg] at h2
  have h3 := (ENat.toENNReal_le.mpr h2).trans hB
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast] at h3
  exact (ENNReal.ofReal_le_ofReal_iff hB0).mp h3

theorem exists_avoid (P : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) (A₁ A₂ : ℕ → Prop)
    [DecidablePred A₁] [DecidablePred A₂] {M t : ℝ} (hP : 0 < (P.card : ℝ)) (ht : 0 < t)
    (hM : (∑ q ∈ P, f q) / P.card ≤ M) (hMt : 4 * M ≤ t)
    (h₁ : 4 * ((P.filter A₁).card : ℝ) ≤ P.card) (h₂ : 4 * ((P.filter A₂).card : ℝ) ≤ P.card) :
    ∃ q ∈ P, f q ≤ t ∧ ¬ A₁ q ∧ ¬ A₂ q := by
  by_contra hc
  have hsub : P ⊆ (P.filter (fun q => t < f q) ∪ P.filter A₁) ∪ P.filter A₂ := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_filter]
    by_contra hn
    apply hc
    refine ⟨q, hq, ?_, ?_, ?_⟩
    · by_contra h; exact hn (Or.inl (Or.inl ⟨hq, not_le.mp h⟩))
    · intro h; exact hn (Or.inl (Or.inr ⟨hq, h⟩))
    · intro h; exact hn (Or.inr ⟨hq, h⟩)
  have hc1 : P.card ≤ (P.filter (fun q => t < f q)).card + (P.filter A₁).card
      + (P.filter A₂).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc2 : (P.card : ℝ) ≤ (P.filter (fun q => t < f q)).card + (P.filter A₁).card
      + (P.filter A₂).card := by exact_mod_cast hc1
  have h3 : ((P.filter (fun q => t < f q)).card : ℝ) * t ≤ ∑ q ∈ P, f q := by
    calc ((P.filter (fun q => t < f q)).card : ℝ) * t
        = ∑ _q ∈ P.filter (fun q => t < f q), t := by simp
      _ ≤ ∑ q ∈ P.filter (fun q => t < f q), f q :=
          Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp hq).2.le
      _ ≤ ∑ q ∈ P, f q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun q _ _ => hf q
  rw [div_le_iff₀ hP] at hM
  have h4 : 4 * ((P.filter (fun q => t < f q)).card : ℝ) * t ≤ P.card * t := by nlinarith
  have h5 := le_of_mul_le_mul_right h4 ht
  linarith

theorem eventually_sizes {eps : ℝ} (he : 0 < eps) (C₁ C : ℝ) :
    ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ 2 ≤ x ^ (eps / 5) ∧
      (1 / 4) * Real.log x ^ 2 * Real.log 8 ≤ x ^ (eps / 5) ∧
      Real.log 8 + x ^ (eps / 5) ≤ x ^ (eps / 4) ∧
      4 * (C₁ * (8 * Real.exp (x ^ (eps / 5))) ^ ((1 : ℝ) / 4)) ≤
        Real.exp (x ^ (eps / 5)) ^ ((9 : ℝ) / 10) ∧
      16 * C * Real.log x ≤ x ^ (2 * eps) := by
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have t5 : Tendsto (fun x : ℝ => x ^ (eps / 5)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have t20 : Tendsto (fun x : ℝ => x ^ (eps / 20)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have tE : Tendsto (fun x : ℝ => Real.exp (x ^ (eps / 5)) ^ ((13 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (Real.tendsto_exp_atTop.comp t5)
  have o1 := (isLittleO_log_rpow_rpow_atTop (s := eps / 5) 2 (by positivity)).bound
    (c := 4 / Real.log 8) (by positivity)
  have o2 := (isLittleO_log_rpow_atTop (r := 2 * eps) (by positivity)).bound
    (c := 1 / (16 * |C| + 1)) (by positivity)
  filter_upwards [eventually_ge_atTop (4 : ℝ), t5.eventually_ge_atTop 2,
    t5.eventually_ge_atTop (Real.log 8), t20.eventually_ge_atTop 2,
    tE.eventually_ge_atTop (4 * |C₁| * 8 ^ ((1 : ℝ) / 4)), o1, o2] with x h4 h2 h8 h20 hE b1 b2
  have hx : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  refine ⟨h4, h2, ?_, ?_, ?_, ?_⟩
  · rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      Real.rpow_two, div_mul_eq_mul_div, le_div_iff₀ hl8] at b1
    linarith
  · have : x ^ (eps / 4) = x ^ (eps / 5) * x ^ (eps / 20) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    rw [this]; nlinarith
  · have hX : 0 < Real.exp (x ^ (eps / 5)) := Real.exp_pos _
    have : Real.exp (x ^ (eps / 5)) ^ ((9 : ℝ) / 10) =
        Real.exp (x ^ (eps / 5)) ^ ((13 : ℝ) / 20) * Real.exp (x ^ (eps / 5)) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hX]; norm_num
    rw [this, Real.mul_rpow (by norm_num) hX.le]
    have h0 : 0 ≤ Real.exp (x ^ (eps / 5)) ^ ((1 : ℝ) / 4) := by positivity
    have h1 : 4 * C₁ * 8 ^ ((1 : ℝ) / 4) ≤ 4 * |C₁| * 8 ^ ((1 : ℝ) / 4) := by
      gcongr; exact le_abs_self _
    calc _ = (4 * C₁ * 8 ^ ((1 : ℝ) / 4)) * Real.exp (x ^ (eps / 5)) ^ ((1 : ℝ) / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (h1.trans hE) h0
  · rw [Real.norm_of_nonneg hlx, Real.norm_of_nonneg (by positivity),
      div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at b2
    have := le_abs_self C
    nlinarith

theorem exists_prime_good_bounds : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q : ℕ, q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < q ∧ (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧ ∀ d : ℕ, d.Prime → d % 4 = 3 → q ≠ d → GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir q) (8 * q * d) ∧ GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧ BoundsAtX x eps C (GlobalTheoryTheory.psDir q) (8 * q * d) := by
  classical
  intro hEZ hEC hLD hZC hZF hTZ hPg hJu eps he he'
  obtain ⟨C₁, hC₁, hbad⟩ := GlobalTheory.FewBadChars.badChars_count_of_density hJu
  obtain ⟨x₁, C, hC, hG⟩ := GlobalTheory.T.g_chi_approximation_sum hEZ hEC hLD hZC hZF eps he he'
  obtain ⟨x₂, hcard⟩ := GlobalTheory.Mem.An.card_primes_residue_ge_rpow hTZ eps he he'
  obtain ⟨x₃, C₃, hmean⟩ := GlobalTheory.T.multiplicative_weight_prime_sum hTZ hPg hZF eps he he'
  obtain ⟨x₄, hsz⟩ := Filter.eventually_atTop.mp (eventually_sizes he C₁ C₃)
  refine ⟨max (max x₁ x₂) (max x₃ x₄), C, hC, fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx₁, hx₂⟩, hx₃, hx₄⟩ := hx
  obtain ⟨h4, h2, hlog, hQ4, hBP, hCx⟩ := hsz x hx₄
  have hx0 : 0 < x := by linarith
  have hXdef : GlobalTheoryTheory.X1 x eps = Real.exp (x ^ (eps / 5)) := rfl
  rw [← hXdef] at hBP
  set X := GlobalTheoryTheory.X1 x eps with hX
  have hX1 : 1 ≤ X := by rw [hXdef]; exact Real.one_le_exp (by linarith)
  have hX0 : 0 < X := by linarith
  have hlX : Real.log X = x ^ (eps / 5) := by rw [hXdef, Real.log_exp]
  have h65 : x ^ (eps / 6) ≤ x ^ (eps / 5) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hH1 : (1 / 4) * Real.log x ^ 2 * Real.log ((8 : ℕ) : ℝ) ≤ Real.log X := by
    rw [hlX]; exact_mod_cast hlog
  have hH2 : x ^ (eps / 6) ≤ Real.log X := hlX ▸ h65
  have hPc := hcard x hx₂ 8 3 (by norm_num) (by norm_num) X hX0 hH1 hH2
  have hm := hmean x hx₃ 8 3 dvd_rfl (by norm_num) (by norm_num) (by norm_num)
    (fun p hp hd => Or.inl (by
      have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from hd)
      have : (p : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_dvd two_pos this
      linarith)) X hX0 hH1 hH2 (fun _ => 1) rfl (fun _ _ => (mul_one _).symm) (fun _ => by simp)
  set P := Formalism.HermitianLattices.GL2PrimeSums.PP 8 3 X with hP
  have hmem : ∀ q ∈ P, q.Prime ∧ q % 8 = 3 ∧ Real.sqrt X < q ∧ (q : ℝ) ≤ X := by
    intro q hq
    simp only [hP, Formalism.HermitianLattices.GL2PrimeSums.PP, Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨ha, hb⟩, hp, hm⟩ := hq
    exact ⟨hp, hm, (Nat.floor_lt (Real.sqrt_nonneg _)).mp ha, (Nat.le_floor_iff hX0.le).mp hb⟩
  have hB := hbad (8 * X) (by linarith)
  have hB0 : 0 ≤ C₁ * (8 * X) ^ ((1 : ℝ) / 4) := by positivity

  have fam1 : ∀ q d : ℕ, q.Prime → q % 8 = 3 → d.Prime → d % 4 = 3 → q ≠ d →
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        GlobalTheoryTheory.Induces χ (GlobalTheoryTheory.psDir q) (8 * q * d) → N = q ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
          GlobalTheoryTheory.IsRealChar χ ∧ ∀ a : ℕ, 0 < a → χ (a : ZMod N) = GlobalTheoryTheory.psDir q a := by
    intro q d hq hq8 hd hd4 hqd N _ χ hχ
    have := GlobalTheory.QuadPrim.main q d hq hd (by omega) hd4 hqd 1 0 0 (by simp) N χ (by simpa using hχ)
    simpa using this
  have fam2 : ∀ q d : ℕ, q.Prime → q % 8 = 3 → d.Prime → d % 4 = 3 → q ≠ d →
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        GlobalTheoryTheory.Induces χ (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) →
          N = 8 * q ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧ GlobalTheoryTheory.IsRealChar χ := by
    intro q d hq hq8 hd hd4 hqd N _ χ hχ
    obtain ⟨a, b, c, e, -⟩ :=
      GlobalTheory.QuadPrim.main q d hq hd (by omega) hd4 hqd 1 0 1 (by simp) N χ (by simpa using hχ)
    exact ⟨by simpa using a, b, c, e⟩
  have hs0 : 0 < x ^ (1 / 2 + eps) := Real.rpow_pos_of_pos hx0 _
  obtain ⟨q, hqP, hqS, hq1, hq2⟩ := exists_avoid P
    (fun p => ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) p‖ ^ 2) (fun _ => by positivity)
    (fun q => ∃ d : ℕ, d.Prime ∧ d % 4 = 3 ∧ q ≠ d ∧
      ¬ GoodAllFor (8 * X) (GlobalTheoryTheory.psDir q) (8 * q * d))
    (fun q => ∃ d : ℕ, d.Prime ∧ d % 4 = 3 ∧ q ≠ d ∧
      ¬ GoodAllFor (8 * X) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d))
    (t := (x ^ (1 / 2 + eps) / 2) ^ 2)
    (lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hPc) (by positivity) hm
    (by
      have : (x ^ (1 / 2 + eps)) ^ 2 = x * x ^ (2 * eps) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_one_add' hx0.le (by positivity)]
        congr 1; push_cast; ring
      rw [div_pow, this]
      nlinarith)
    (by
      refine le_trans ?_ (hBP.trans hPc)
      refine mul_le_mul_of_nonneg_left (card_le_of_levels hB0 hB _ id Function.injective_id ?_)
        (by norm_num)
      intro q hq
      obtain ⟨hqP, d, hd, hd4, hqd, hn⟩ := Finset.mem_filter.mp hq
      obtain ⟨hp, h8, -, hle⟩ := hmem q hqP
      by_contra hc
      refine hn fun N _ χ hχ => ?_
      obtain ⟨a, b, c, e, -⟩ := fam1 q d hp h8 hd hd4 hqd N χ hχ
      by_contra hb
      subst a
      exact hc (level_mem_bad (N := N) χ (by linarith) hχ.1 b e c hb))
    (by
      refine le_trans ?_ (hBP.trans hPc)
      refine mul_le_mul_of_nonneg_left (card_le_of_levels hB0 hB _ (fun q => 8 * q)
        (mul_right_injective₀ (by norm_num)) ?_) (by norm_num)
      intro q hq
      obtain ⟨hqP, d, hd, hd4, hqd, hn⟩ := Finset.mem_filter.mp hq
      obtain ⟨hp, h8, -, hle⟩ := hmem q hqP
      by_contra hc
      refine hn fun N _ χ hχ => ?_
      obtain ⟨a, b, c, e⟩ := fam2 q d hp h8 hd hd4 hqd N χ hχ
      by_contra hb
      subst a
      exact hc (level_mem_bad χ (by push_cast; linarith) hχ.1 b e c hb))
  obtain ⟨hp, h8, hlo, hle⟩ := hmem q hqP
  refine ⟨q, hp, h8, hlo, hle, fun d hd hd4 hqd => ?_⟩
  have g1 : GoodAllFor (8 * X) (GlobalTheoryTheory.psDir q) (8 * q * d) := by
    by_contra h; exact hq1 ⟨d, hd, hd4, hqd, h⟩
  have g2 : GoodAllFor (8 * X) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) := by
    by_contra h; exact hq2 ⟨d, hd, hd4, hqd, h⟩
  refine ⟨g1, g2, fun N _ χ hχ => ?_⟩
  obtain ⟨-, -, hne, -, hval⟩ := fam1 q d hp h8 hd hd4 hqd N χ hχ
  have hlQ : Real.log (8 * X) = Real.log 8 + x ^ (eps / 5) := by
    rw [Real.log_mul (by norm_num) hX0.ne', hlX]
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  obtain ⟨k1, k2⟩ := hG x hx₁ (8 * X) N χ (by positivity) (by rw [hlQ]; linarith)
    (by rw [hlQ]; exact hQ4) hne (g1 N χ hχ)
  refine ⟨?_, k2⟩
  have hS : ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod N) =
      Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.sqSum
    refine Finset.sum_congr (by first | rfl | simp) fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [hval n hn0, GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron,
      GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 q n (by omega) hn0, mul_one]
    rfl
  rw [hS] at k1
  have k3 : ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q‖ ≤ x ^ (1 / 2 + eps) / 2 :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hqS
  have k4 : x ^ eps ≤ x ^ (1 / 2 + eps) / 2 := by
    have : (2 : ℝ) ≤ x ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le (by linarith)
    have h0 : 0 < x ^ eps := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_add hx0]; nlinarith
  have k5 := norm_sub_le (GlobalTheoryTheory.gChi χ x + Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q)
    (Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q)
  rw [add_sub_cancel_right] at k5
  linarith

end GlobalTheory.ChoiceOfModulus
