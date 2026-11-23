import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.BadCount
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMeanOfInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreePrimeRemoval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyChangeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundFromExactAsymptotic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantDivisorBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorAlgebraicStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open GlobalTheory.CovHt (DeRhamMinusHodgeTateGoodPrimesAt DeRhamHodgeTateDifferenceKilledAt)

noncomputable section

namespace GlobalTheory.MeanOne

open GlobalTheory.LatChange in

theorem one_term_at (D : D7) (Y : ShimX D.what₂.Tau) (h3 : DeRhamMinusHodgeTateGoodPrimesAt Y) (ht : DeRhamHodgeTateDifferenceKilledAt Y) (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (hp : p.Prime)
    (hd : ¬ p ∣ 2 * dE D) (hl : p ∉ Y.lev) (τ : D.what₂.Tau) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ Y.N)
    (Q : Pol D.what₂.Tau Y.N) (hQ : Q.IsHomogeneous (dimY Y + 1 - k)) :
    Y.arDeg (Sx.erase p) R (pSum τ k * Q) - Y.arDeg (insert p Sx) R (pSum τ k * Q) =
      Real.log p * ((Nat.factorial k : ℝ) * ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * Q)) -
        Real.log p / ((p : ℝ) - 1) * ((k : ℝ) * Y.chern (pLow Y.j τ (k - 1) * Q)) := by
  have hp2 : p ≠ 2 := by rintro rfl; exact hd (dvd_mul_right _ _)
  have hu : UnramE D p := fun h => hd (Dvd.dvd.mul_left h 2)
  have hm : dimY Y + 1 - k + k = dimFl D.what₂.Tau Y.N + 1 :=
    Nat.sub_add_cancel (le_dim _ τ _ _ hkN)
  have e1 := h3 Sx R p hp hp2 hu hl τ k hk _ hm _ (tagDR_whom _ _ _ Q hQ)
  have e2 := ht Sx R p hp τ k hk Q
  rw [collapse_tagDR] at e1
  have hf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hf' : (Nat.factorial (k - 1) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfk : (Nat.factorial k : ℝ) = k * (Nat.factorial (k - 1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega)).symm
  rw [← Y.arMix_DR, ← Y.arMix_HT, ← map_sub]
  have key : tagDR D.what₂.Tau Y.N (pSum τ k * Q) - tagHT D.what₂.Tau Y.N (pSum τ k * Q) =
      (Nat.factorial k : ℝ) • ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * tagDR D.what₂.Tau _ Q) +
        tagHT D.what₂.Tau _ (pk D _ τ k) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q) := by
    rw [← smul_eq_C_mul, map_smul, map_smul, ← smul_sub, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hf, one_smul,
      map_mul, map_mul]
    change tagDR _ _ (pk D _ τ k) * _ - tagHT _ _ (pk D _ τ k) * _ = _
    ring
  rw [key, map_add, map_smul, e1, e2, add_zero]
  have e3 : Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * Q) =
      (Nat.factorial (k - 1) : ℝ)⁻¹ * Y.chern (pLow Y.j τ (k - 1) * Q) := by
    rw [← smul_eq_mul (Nat.factorial (k - 1) : ℝ)⁻¹, ← map_smul, smul_eq_C_mul, ← mul_assoc]
    rfl
  rw [e3, smul_eq_mul]
  generalize (∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * Q)) = T
  rw [hfk]
  have : (Nat.factorial (k - 1) : ℝ) * (Nat.factorial (k - 1) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hf'
  linear_combination (-(Real.log p / ((p : ℝ) - 1) * k *
    Y.chern (pLow Y.j τ (k - 1) * Q))) * this

open GlobalTheory.LatChange in

theorem lattice_change_at : ∀ (D : D7) (Y : ShimX D.what₂.Tau), DeRhamMinusHodgeTateGoodPrimesAt Y → DeRhamHodgeTateDifferenceKilledAt Y → Propor Y → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime → ¬ p ∣ 2 * dE D → p ∉ Y.lev → ∀ Q, Cof Y Q → Y.arDeg (Sx.erase p) R (comb _ Q) - Y.arDeg (insert p Sx) R (comb _ Q) = -(Real.log p / ((p : ℝ) - 1)) * Y.vol * shAll _ (comb _ Q) + Real.log p / Y.N * Y.vol * (∑ τ, kap Y p τ * totF τ (comb _ Q)) + restTerm Y p Q := by
  intro D Y h3 ht h10 Sx R p hp hd hl Q hQ
  have hjN := Y.j_lt
  have hN : 1 ≤ Y.N := by omega
  have hN' : (Y.N : ℝ) ≠ 0 := by exact_mod_cast (by omega : Y.N ≠ 0)
  have hc : ∀ Q, Y.chern Q = Y.vol * degFl D.what₂.Tau Y.N Q := h10
  have hF := fun τ => GlobalTheory.T.shift_functional_decomposition D.what₂.Tau Y.N Y.j Q τ hN
  have hI : Finset.Icc 1 Y.N = insert 1 (Finset.Icc 2 Y.N) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have lhs : Y.arDeg (Sx.erase p) R (comb _ Q) - Y.arDeg (insert p Sx) R (comb _ Q) =
      ∑ τ, ∑ k ∈ Finset.Icc 1 Y.N, (Y.arDeg (Sx.erase p) R (pSum τ k * Q τ k) -
        Y.arDeg (insert p Sx) R (pSum τ k * Q τ k)) := by
    simp only [comb, map_sum, Finset.sum_sub_distrib]
  rw [lhs]
  unfold shAll restTerm
  simp only [Finset.mul_sum (s := Finset.univ)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.sum_congr rfl (fun k hk => one_term_at D Y h3 ht Sx R p hp hd hl τ k (Finset.mem_Icc.1 hk).1
    (Finset.mem_Icc.1 hk).2 (Q τ k) (hQ τ k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2)), Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have s1 : ∑ k ∈ Finset.Icc 1 Y.N, (k : ℝ) * Y.chern (pLow Y.j τ (k - 1) * Q τ k) =
      Y.vol * shF Y.j τ (comb _ Q) := by
    unfold comb
    rw [(hF τ).1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hc]; ring
  have s2 : (∑' n : ℕ, ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) *
      Y.chern (chLie Y.j (1 - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * Q τ 1)) =
      kap Y p τ * (Y.vol * degFl D.what₂.Tau Y.N (Q τ 1)) := by
    unfold kap
    rw [← tsum_mul_right]
    refine tsum_congr (fun n => ?_)
    rw [Nat.sub_self, chLie_zero _ _ hjN.le, ← smul_eq_C_mul, map_smul, smul_eq_mul, hc, pow_one, mul_assoc]
  have s3 : totF τ (comb Y Q) = (Y.N : ℝ) * degFl D.what₂.Tau Y.N (Q τ 1) := (hF τ).2
  rw [s1, s3, hI, Finset.sum_insert (by simp), s2]
  simp only [Nat.factorial_one, Nat.cast_one, one_mul]
  field_simp
  ring

theorem change_at : ∀ (D : D7) (Y : ShimX D.what₂.Tau), DeRhamMinusHodgeTateGoodPrimesAt Y → DeRhamHodgeTateDifferenceKilledAt Y → Propor Y → ∀ Φ : ℝ → Fn Y, LimFam Φ → Change Φ := by
  intro D Y h3 h4 h5 Φ hΦ B₀ B hB₀ hB Q hQ
  obtain ⟨hsub, -, hnew, -⟩ := GlobalTheory.T.new_primes_set_description D Y B₀ B (by linarith)
  have hU : setB Y B₀ ∪ newPrimes Y B₀ B = setB Y B :=
    Finset.union_sdiff_of_subset (hsub hB)
  have t0 := hΦ B₀ hB₀ (comb _ Q)
  have t1 := hΦ B (hB₀.trans hB) (comb _ Q)
  refine tendsto_nhds_unique t0 ((t1.add_const _).congr fun R => ?_)
  have key := telescope_finset (fun Sx => Y.arDeg Sx R (comb _ Q)) _
    (setB Y B₀) (newPrimes Y B₀ B) Finset.disjoint_sdiff
    (fun p hp Sx => lattice_change_at D Y h3 h4 h5 Sx R p ((hnew p).1 hp).1 ((hnew p).1 hp).2.2.2.1
      ((hnew p).1 hp).2.2.2.2 Q hQ)
  rw [hU] at key
  exact key.symm

def TailAt {D : D7} (Y : ShimX D.what₂.Tau) (C5 : ℝ) : Prop := ∀ u g, WeightHyp Y u g →
  ∀ Qs : D.what₂.Tau → ℕ → MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    (∀ τ k, 1 ≤ k → k ≤ Y.N → (Qs τ k).IsHomogeneous (dimY Y + 1 - k)) →
    linRoot u ^ (dimY Y + 1) =
      ∑ τ, ∑ k ∈ Finset.Icc 1 Y.N, pk D _ τ k * Qs τ k →
    ∀ B : ℕ, (∑ p ∈ (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧
        bigB0 Y u g < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev),
      Real.log p * ∑ τ, ∑ k ∈ Finset.Icc 2 Y.N, ∑' n : ℕ,
        |(Nat.factorial k : ℝ) * ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            Qs τ k) / (((dimY Y : ℝ) + 1) * geoDeg Y u)|) ≤
    C5 * jS Y * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

def TailWeakAt {D : D7} (Y : ShimX D.what₂.Tau) (C5 : ℝ) : Prop := ∀ u g, WeightHyp Y u g →
  ∀ Qs : D.what₂.Tau → ℕ → MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    (∀ τ k, 1 ≤ k → k ≤ Y.N → (Qs τ k).IsHomogeneous (dimY Y + 1 - k)) →
    linRoot u ^ (dimY Y + 1) =
      ∑ τ, ∑ k ∈ Finset.Icc 1 Y.N, pk D _ τ k * Qs τ k →
    ∀ B : ℕ, (∑ p ∈ (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧
        bigB0 Y u g < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev),
      |Real.log p * (∑ τ, ∑ k ∈ Finset.Icc 2 Y.N, (Nat.factorial k : ℝ) *
        ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            Qs τ k)) / (((dimY Y : ℝ) + 1) * geoDeg Y u)|) ≤
    C5 * jS Y * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

open Finset GlobalTheory.FlagHook GlobalTheory.TailBound in

theorem tail_at (D : D7) (Y : ShimX D.what₂.Tau) (h10 : Propor Y) : TailAt Y (8 * Real.log 4) := by
  have hc : ∀ Q, Y.chern Q = Y.vol * degFl D.what₂.Tau Y.N Q := h10
  intro u g hW Qs hQ hdec B
  obtain ⟨hg, hreg, -, hsep⟩ := hW
  obtain ⟨hH, hB⟩ := big_b0_lower_bound Y u g hg
  have hN : (2 : ℝ) ≤ Y.N := by
    have h1 := Y.j_pos
    have h2 := Y.j_lt
    exact_mod_cast (by omega : 2 ≤ Y.N)
  have hB16 : 16 ≤ bigB0 Y u g := by nlinarith
  generalize bigB0 Y u g = B0 at hB hB16 ⊢
  have hdec' : IsDecomp u Qs := ⟨hQ, hdec⟩
  have hne : ∀ τ a b, a ≠ b → u τ a ≠ u τ b := fun τ a b hab => by
    rcases lt_or_gt_of_ne hab with h | h
    · exact (hreg τ a b h).ne'
    · exact (hreg τ b a h).ne
  set U : D.what₂.Tau → ℝ := fun τ => (⨆ i, u τ i) - ⨅ i, u τ i with hU
  have hU0 : ∀ τ, 0 ≤ U τ := fun τ => (spread_spec Y u τ).2.1
  have hkap : ∀ τ k, 2 ≤ k → k ≤ Y.N → ∀ τ' i, inSmall Y i →
      |GlobalTheory.FlagHook.kap u k (X (τ', i) ^ (k - 1)) (Qs τ k)| ≤ U τ * (B0 / 2) ^ (k - 1) := by
    intro τ k hk hkN τ' i hi
    refine (GlobalTheory.T.kappa_hook_bound _ Y.N u Qs g (U τ) τ τ' i k hg hne hdec' hk hkN (spread_spec Y u τ).1
      (fun a ha => hsep τ' i a hi (Ne.symm ha))).trans ?_
    have h1 : U τ / g ≤ 2 * (supAbs Y u / g) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (spread_spec Y u τ).2.2 hg.le
    have h2 : 0 ≤ U τ / g := div_nonneg (hU0 τ) hg.le
    have h3 : (2 * ((Y.N : ℝ) * (1 + U τ / g))) ^ (k - 1) ≤ (B0 / 2) ^ (k - 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      nlinarith
    have h4 : (2 : ℝ) ^ (k - 1) / (k.factorial : ℝ) ≤ 2 ^ (k - 1) :=
      div_le_self (by positivity) (by exact_mod_cast k.factorial_pos)
    have h5 := hU0 τ
    calc _ ≤ 2 ^ (k - 1) * U τ * ((Y.N : ℝ) * (1 + U τ / g)) ^ (k - 1) := by gcongr
      _ = U τ * (2 * ((Y.N : ℝ) * (1 + U τ / g))) ^ (k - 1) := by rw [mul_pow 2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 h5
  have hSU : 0 ≤ ∑ τ, U τ := sum_nonneg fun τ _ => hU0 τ
  have hc0 : 0 ≤ 2 * B0 * (jS Y : ℝ) * ∑ τ, U τ := by positivity
  calc _ ≤ ∑ p ∈ (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧
        B0 < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev),
          (2 * B0 * (jS Y : ℝ) * ∑ τ, U τ) * (Real.log p / (p : ℝ) ^ 2) := by
        refine sum_le_sum fun p hp => ?_
        have hp1 : B0 < (p : ℝ) := (mem_filter.1 hp).2.2.1
        have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        calc _ ≤ Real.log p * ∑ τ, 4 * ((jS Y : ℝ) * U τ) * (B0 / 2) / (p : ℝ) ^ 2 := by
              refine mul_le_mul_of_nonneg_left (sum_le_sum fun τ _ => ?_) hl
              refine sum_tsum_abs_le (p : ℝ) (B0 / 2) _ (by linarith) (by linarith) (by linarith)
                (mul_nonneg (Nat.cast_nonneg _) (hU0 τ)) Y.N _ ?_
              intro k hk n
              obtain ⟨hk2, hkN⟩ := mem_Icc.1 hk
              refine (abs_term_le Y hc u k (by omega) _ (by positivity) _ _).trans ?_
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [mul_assoc]
              exact abs_kap_chLie_le Y u k (k - 1) (by omega) _ _ _ (hkap τ k hk2 hkN)
          _ = _ := by
              rw [mul_sum, mul_sum, sum_mul]
              refine sum_congr rfl fun τ _ => ?_
              ring
    _ ≤ (2 * B0 * (jS Y : ℝ) * ∑ τ, U τ) * (4 * Real.log 4 / B0) := by
        rw [← mul_sum]
        refine mul_le_mul_of_nonneg_left (le_trans ?_ (GlobalTheory.sum_log_div_sq_primes_tail B0 B (by linarith))) hc0
        refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ =>
          div_nonneg (Real.log_natCast_nonneg p) (by positivity)
        intro p hp
        rw [mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    _ = _ := by
        have : B0 ≠ 0 := by linarith
        field_simp
        ring

open GlobalTheory.NefComparisonAlg in

theorem weak_tail_at {D : D7} (Y : ShimX D.what₂.Tau) (C5 : ℝ) : TailAt Y C5 → TailWeakAt Y C5 := by
  intro h u g hu Qs hQ hdec B
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) (h u g hu Qs hQ hdec B)
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [mul_div_assoc, abs_mul, abs_of_nonneg hlog]
  refine mul_le_mul_of_nonneg_left ?_ hlog
  rw [Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
  rw [Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk2 : 2 ≤ k := (Finset.mem_Icc.1 hk).1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  exact abs_tsum_geom_le
    (fun σ : EmbC D => Y.chern (chLie Y.j (k - 1) σ * Qs τ k))
    (fun n => frobEmb D p (n + 1) (Sum.inl τ)) _ _ _ (by positivity) (inv_lt_one_of_one_lt₀ hpk)

theorem lower_at : ∀ r Cf C5 : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Y : ShimX D.what₂.Tau), 2 < D.R.f * (Y.N - 1) → Propor Y → TailWeakAt Y C5 → FewBad Y → ∀ (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y), Degrees A → FlagHt D.what₂.Tau _ hh → FlatVal A Φ → FlatBd Y Cf → TestVal Φ hh r → (∀ B₀ : ℝ, 2 ≤ B₀ → ∃ a b : ℝ, ExactAt Φ hh B₀ a b) → Lower Φ C := by
  intro r Cf C5
  obtain ⟨C₁, hC₁, hA0⟩ := GlobalTheory.T.lower_bound_linear_coefficient r
  refine ⟨C₁ + max Cf 0 + max C5 0, add_nonneg (add_nonneg hC₁ (le_max_right _ _)) (le_max_right _ _), ?_⟩
  intro D Y hf hProp h5 hFew A Φ hh hDeg hFl hFV hFB hTV hEx u g hW
  have h5w := h5 u g hW
  obtain ⟨h48', -, hlg⟩ := GlobalTheory.T.threshold_and_log_comparison D Y hf
  have h48 := h48' u g hW
  set B₀ := bigB0 Y u g with hB₀
  obtain ⟨a, b, hab⟩ := hEx B₀ (by linarith)
  have hvol : 0 < Y.vol := by
    rw [hDeg.2.1]
    haveI := Y.compNe
    exact Finset.sum_pos (fun c _ => hDeg.1 c) Finset.univ_nonempty
  have ha := hA0 D Y Φ hh B₀ a b h48 hvol hProp hFew hTV hab
  have hK := GlobalTheory.T.flat_value_coefficient_bound D Y A Φ hh Cf B₀ a b h48 hDeg hFl hFV hFB hab
  have hreg : RegDom u := hW.2.1
  have hdom : Dom u := by
    intro τ x y hxy
    rcases hxy.eq_or_lt with h | h
    · rw [h]
    · exact (hreg τ x y h).le
  have hfd : 0 < flagDeg D.what₂.Tau Y.N u := (GlobalTheory.T.flag_degree_pos_regular_dominant _ _ u).1 hreg
  have hgeo : geoDeg Y u = Y.vol * flagDeg D.what₂.Tau Y.N u := hProp _
  have hgpos : 0 < geoDeg Y u := by rw [hgeo]; positivity
  obtain ⟨Q, hQ, hF⟩ := GlobalTheory.T.power_sum_decomposition_homogeneous D.what₂.Tau Y.N _ (linRoot_pow_homog_lower u (dimFl D.what₂.Tau Y.N + 1))
  have hcomb : comb Y Q = linRoot u ^ (dimFl D.what₂.Tau Y.N + 1) := hF.symm
  have hlim := hab Q hQ
  have h5' := h5w Q hQ hF
  have hN : 0 < Y.N := by have := Y.j_lt; omega
  have hNR : (0 : ℝ) < Y.N := by exact_mod_cast hN
  set D1 : ℝ := (dimY Y : ℝ) + 1 with hD1
  have hD1pos : 0 < D1 := by positivity
  set Wd : ℝ := (jS Y : ℝ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i) with hWd
  have hWd0 : 0 ≤ Wd := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro τ _
    have h1 : u τ ⟨0, hN⟩ ≤ ⨆ i, u τ i := le_ciSup (Set.finite_range _).bddAbove _
    have h2 : ⨅ i, u τ i ≤ u τ ⟨0, hN⟩ := ciInf_le (Set.finite_range _).bddBelow _
    linarith
  have hpart : ∀ B : ℕ, |∑ p ∈ newPrimes Y B₀ B, restTerm Y p Q| ≤ max C5 0 * D1 * geoDeg Y u * Wd := by
    intro B
    have h1 := h5' B
    rw [← (GlobalTheory.T.new_primes_set_description D Y B₀ B (by linarith)).2.2.2 B] at h1
    have h2 : ∑ p ∈ newPrimes Y B₀ B, |restTerm Y p Q / (D1 * geoDeg Y u)| ≤ C5 * jS Y * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i) := h1
    have hpos : 0 < D1 * geoDeg Y u := by positivity
    have h3 : ∑ p ∈ newPrimes Y B₀ B, |restTerm Y p Q / (D1 * geoDeg Y u)| =
        (∑ p ∈ newPrimes Y B₀ B, |restTerm Y p Q|) / (D1 * geoDeg Y u) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [abs_div, abs_of_pos hpos]
    rw [h3, mul_assoc, ← hWd, div_le_iff₀ hpos] at h2
    calc _ ≤ ∑ p ∈ newPrimes Y B₀ B, |restTerm Y p Q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ C5 * Wd * (D1 * geoDeg Y u) := h2
      _ ≤ max C5 0 * Wd * (D1 * geoDeg Y u) := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  have hrest := le_of_tendsto' hlim.abs hpart
  rw [hcomb] at hrest
  have hlog : 0 ≤ Real.log B₀ := Real.log_nonneg (by linarith)
  have hlgB := hlg B₀ (by linarith)
  have hK' : |(Y.j : ℝ) * a + Y.N * b| ≤ max Cf 0 * Y.N * lg D B₀ := by
    refine hK.trans ?_
    have : 0 ≤ lg D B₀ := hlog.trans hlgB
    gcongr
    exact le_max_left _ _
  have hh0 : 0 ≤ Y.vol * hh (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1)) := mul_nonneg hvol.le (hFl.2.1 u hdom)
  have hlgB' : Real.log B₀ + Real.log D.host.rdE ≤ lg D B₀ := by
    have h1 := (GlobalTheory.T.threshold_and_log_comparison D Y hf).2.1
    unfold lg
    rw [Real.log_mul (by linarith) (by linarith)]
    linarith [abs_nonneg (dlogL D 1)]
  have key := GlobalTheory.lowerBound_numerical_end D.what₂.Tau (Φ B₀ (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1)))
    (Y.vol * hh (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1))) (geoDeg Y u) D1 a ((Y.j : ℝ) * a + Y.N * b) _
    (Real.log B₀ + Real.log D.host.rdE) (lg D B₀) Wd
    (fun τ => (∑ i ∈ Finset.univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j), u τ i) - Y.j * ((∑ i, u τ i) / Y.N))
    (fun τ => (∑ i, u τ i) / Y.N) (fun τ => ∑ i, |u τ i|) Y.N C₁ (max Cf 0) (max C5 0) hNR hh0 hgpos.le hD1pos.le
    (add_nonneg hlog D.host.log_rdE_nonneg') hlgB' hWd0 hC₁ (le_max_right _ _) (le_max_right _ _) ?_
    (fun τ => GlobalTheory.centred_block_sum_bounds Y.N Y.j (u τ) Y.j_lt.le hN (hdom τ)) ha hK' hrest
  · unfold atWt
    linarith
  · have hsh : shAll Y (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1)) = -(D1 * flagDeg D.what₂.Tau Y.N u) *
        ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j), u τ i := by
      unfold shAll
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [(GlobalTheory.T.shift_functional_linear_root_power D.what₂.Tau Y.N Y.j u τ).1]
      simp only [hD1, dimY]; ring
    have htot : totAll Y (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1)) = -(D1 * flagDeg D.what₂.Tau Y.N u) *
        ∑ τ, ∑ i, u τ i := by
      unfold totAll
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [(GlobalTheory.T.shift_functional_linear_root_power D.what₂.Tau Y.N Y.j u τ).2]
      simp only [hD1, dimY]; ring
    have hsum : ∑ τ, (a * ((∑ i ∈ Finset.univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j), u τ i) - Y.j * ((∑ i, u τ i) / Y.N)) +
        ((Y.j : ℝ) * a + Y.N * b) * ((∑ i, u τ i) / Y.N)) =
        a * (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j), u τ i) + b * ∑ τ, ∑ i, u τ i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      field_simp
      ring
    rw [hsum, hsh, htot, hgeo]
    ring

theorem slopeMean_at : ∀ r Cf : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Y : ShimX D.what₂.Tau), 2 < D.R.f * (Y.N - 1) →
    DeRhamMinusHodgeTateGoodPrimesAt Y → DeRhamHodgeTateDifferenceKilledAt Y → Propor Y → FewBad Y → ∀ (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y), Inputs A Φ hh r Cf →
      GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.VolEq Y ∧ GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.SlopeMean Y C := by
  intro r Cf
  obtain ⟨C, hC0, hC⟩ := lower_at r Cf (8 * Real.log 4)
  refine ⟨C, hC0, ?_⟩
  intro D Y hf h3 h1t h10 hF A Φ hh hI
  obtain ⟨hLim, hPS, hAg, hPos, hSq, hHt, hDeg, hEq, hAnti, hFl, hRel, hFV, hFB, hTV⟩ := hI
  have hvol : 0 < Y.vol := vol_pos_assembly hDeg
  have hWS := GlobalTheory.T.wall_smallness_of_degrees D _ A hf hPos hSq hHt hDeg
  have hWB := GlobalTheory.T.wall_bound_of_poly_size D _ A Φ hf hPS hAg hWS
  have hT := GlobalTheory.T.shape_of_antisymmetric_family D _ Φ hh hvol hAnti hFl hWB
  have hCc := GlobalTheory.T.shape_change_of_relabelling D _ Φ hh hvol hRel hFl hT
  have hFf := GlobalTheory.T.shape_final_of_shape_change D _ Φ hh hCc
  have hCh := change_at D Y h3 h1t h10 Φ hLim
  have hEx := GlobalTheory.T.exact_asymptotic_exists D _ Φ hh hvol hFf hCh
  have hLow := hC D Y hf h10 (weak_tail_at Y _ (tail_at D Y h10)) hF A Φ hh hDeg hFl hFV hFB hTV hEx
  exact GlobalTheory.T.equal_volume_and_slope_mean D _ A Φ C hf hLim hPS hAg hDeg hEq h10 hLow

end GlobalTheory.MeanOne

end
