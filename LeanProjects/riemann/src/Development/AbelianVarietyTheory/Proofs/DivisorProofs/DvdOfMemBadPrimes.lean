import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.BadLog

theorem logSum_le_log {B : Finset ℕ} {N : ℕ} (hN : N ≠ 0) (h : ∀ p ∈ B, p.Prime ∧ p ∣ N) : logSum B ≤ Real.log N := by
  have h1 : ∏ p ∈ B, p ∣ N :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) fun p hp =>
      Nat.mem_primeFactors.2 ⟨(h p hp).1, (h p hp).2, hN⟩).trans (Nat.prod_primeFactors_dvd N)
  have h0 : ∀ p ∈ B, (p : ℝ) ≠ 0 := fun p hp => by exact_mod_cast (h p hp).1.ne_zero
  unfold logSum
  rw [← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h1)
  exact_mod_cast Finset.prod_pos fun p hp => (h p hp).1.pos

variable {D : D7} {L : SizeData₂ D}

theorem log_level_le (P : ParameterChoice' D L) :
    LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 ≠ 0 ∧
    Real.log ((LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 : ℕ) : ℝ) ≤ (2 * |P.CYL| + 17) * zBase L := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hc0 : LevelStarExponents.condE D ≠ 0 := by
    unfold LevelStarExponents.condE
    exact mul_ne_zero (mul_ne_zero D.host.QS_pos.ne' D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero
  have hc1 : (1 : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hc0
  have hc : Real.log (LevelStarExponents.condE D) ≤ L.sc.L := by
    have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ L.t_win.1
    have a : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ L.sc.b ^ ((1 : ℝ) / 2) :=
      (le_mul_of_one_le_right (by positivity) ht).trans P.condE_le
    have b := Real.log_le_log (by positivity) a
    rw [Real.log_pow, Real.log_rpow hb, Scale.b, Real.log_exp] at b
    push_cast at b
    linarith
  obtain ⟨Y, y1, -, y3, y4⟩ := P.g_Y
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) y1
  have hg0 : ∀ i, (0 : ℝ) < D.host.g i := fun i => hY.trans_le (y4 i).1
  have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have l15 : Real.log 15 ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  have hg : ∀ i, Real.log (D.host.g i) ≤ 1 + |P.CYL| * L.sc.L := fun i => by
    have a := Real.log_le_log (hg0 i) (y4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have b : P.CYL * L.sc.L ≤ |P.CYL| * L.sc.L := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith
  have hz : L.sc.L ≤ zBase L := by
    unfold zBase
    exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf hr)
  refine ⟨mul_ne_zero (mul_ne_zero hc0 (mul_ne_zero ?_ ?_)) (by norm_num), ?_⟩
  · exact_mod_cast (hg0 0).ne'
  · exact_mod_cast (hg0 1).ne'
  have a0 := hg0 0
  have a1 := hg0 1
  push_cast
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul a0.ne' a1.ne']
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hz (by positivity))
  linarith [hg 0, hg 1]

theorem dvd_of_mem_badPrimes {T : Core D} (hQ : T.Q.Pins) {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ} (h : Y.Good e o)
    {p : ℕ} (hp : p ∈ badPrimes T.Q.H Y.d.l₂) : p.Prime ∧ p ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := by
  obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
  refine ⟨hp, ?_⟩
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * 15 ^ e := by rw [← h.pd, h.lev.1.2.1, hQ.2.1.1]
  have key : ∀ a, a ∣ LevelStarExponents.condE D → a ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := fun a ha =>
    (ha.mul_right _).mul_right _
  have cD : ∀ a : ℕ, a.Prime → (a : ℤ) ∣ NumberField.discr D.host.E → a ∣ LevelStarExponents.condE D := D.host.der.discr_primes.1
  have c2 : 2 ∣ LevelStarExponents.condE D := cD 2 Nat.prime_two D.host.der.discr_primes.2.1
  have cd : D.host.d ∣ LevelStarExponents.condE D := cD _ D.host.hyp.2.1 D.host.der.discr_primes.2.2
  rcases h' with rfl | h' | h' | h' | h'
  · exact key _ c2
  · rw [h', hQ.1.1]; exact key _ cd
  · exact key _ (cD p hp (Int.natCast_dvd.2 h'))
  · rw [hM] at h'
    rcases (Nat.Prime.dvd_mul hp).1 h' with h' | h'
    · exact (h'.mul_left _).mul_right _
    · exact (hp.dvd_of_dvd_pow h').mul_left _
  · rw [h.lev.2] at h'
    exact absurd (Nat.dvd_one.1 h') hp.ne_one

theorem logSum_badPrimes_le : Size → Covers fun Fm x _ ι p _ Y _ C => logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ C * zBase (Fm.L x ι) :=
  fun h => Closed.imp h fun Fm _ _ _ => ⟨2 * |Fm.CYL| + 17, by positivity, 0, fun x hx _ ι p _ i _ Y hY => by
    obtain ⟨a, b⟩ := log_level_le (Fm.params x hx ι)
    rw [Fm.params_CYL] at b
    exact (logSum_le_log a fun q hq => dvd_of_mem_badPrimes p.fw.laws.pins hY.1 hq).trans b⟩

end GlobalTheory.BadLog

end
