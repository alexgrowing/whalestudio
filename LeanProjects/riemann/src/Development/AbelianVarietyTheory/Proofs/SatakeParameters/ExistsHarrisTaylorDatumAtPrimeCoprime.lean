import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRangeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimesStatement
open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct

namespace GlobalTheory.GoodPrime

theorem schur (tr nm : ℤ) (M : ℕ) (hM : 0 < M) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - tr * r + nm := by
  by_cases hnm : nm = 0
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := M + 1) (by omega)
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, 0, by simp [hnm]⟩
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpd)
  · set t : ℤ := |tr| + 3
    set g : ℤ := (M : ℤ) ^ 2 * nm * t ^ 2 - tr * M * t + 1
    have ht : 3 ≤ t := by have := abs_nonneg tr; omega
    have hMz : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have hnm1 : 1 ≤ |nm| := Int.one_le_abs hnm
    have hg : 2 ≤ |g| := by
      have h1 : |(M : ℤ) ^ 2 * nm * t ^ 2| = (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h2 : |tr * M * t| = |tr| * M * t := by
        rw [abs_mul, abs_mul, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h3 : |(M : ℤ) ^ 2 * nm * t ^ 2| ≤ |g| + |tr * M * t| + 1 := by
        have : (M : ℤ) ^ 2 * nm * t ^ 2 = g + tr * M * t - 1 := by simp only [g]; ring
        rw [this]
        calc |g + tr * M * t - 1| ≤ |g + tr * M * t| + |(1:ℤ)| := abs_sub _ _
          _ ≤ |g| + |tr * M * t| + 1 := by simpa using abs_add_le g (tr * M * t)
      rw [h1, h2] at h3
      have hat : |tr| = t - 3 := by simp only [t]; ring
      rw [hat] at h3
      have hMt : 3 ≤ (M : ℤ) * t := by nlinarith
      have hk : (M : ℤ) ^ 2 * t ^ 2 ≤ (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        have := mul_le_mul_of_nonneg_right hnm1 (by positivity : (0:ℤ) ≤ (M : ℤ) ^ 2 * t ^ 2)
        linarith
      have hq : 3 ≤ t * ((M : ℤ) - 1) + 3 := by nlinarith
      have hr : 9 ≤ ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) := by nlinarith
      have e : ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) = (M : ℤ) ^ 2 * t ^ 2 - (t - 3) * M * t := by ring
      linarith
    have hg' : (2 : ℤ) ≤ (g.natAbs : ℤ) := by rw [← Int.abs_eq_natAbs]; exact hg
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := g.natAbs) (by omega)
    have hpg : (p : ℤ) ∣ g := Int.natCast_dvd.2 hpd
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, M * nm * t, ?_⟩
    · have hpM : (p : ℤ) ∣ M := Int.natCast_dvd_natCast.2 h
      have : (p : ℤ) ∣ g - M * (M * nm * t ^ 2 - tr * t) := dvd_sub hpg (dvd_mul_of_dvd_left hpM _)
      have e : g - M * (M * nm * t ^ 2 - tr * t) = 1 := by simp only [g]; ring
      rw [e] at this
      exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this
    · have e : ((M : ℤ) * nm * t) ^ 2 - tr * (M * nm * t) + nm = nm * g := by simp only [g]; ring
      rw [e]; exact dvd_mul_of_dvd_right hpg _

theorem exists_datum (G : GDatum) (N : ℕ) (hN : 0 < N) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  haveI := G.freeLa; haveI := G.finLa
  obtain ⟨e, he, hperf⟩ := GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range G.La G.EF G.nondeg
  obtain ⟨M, hM, hsplit⟩ := GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes G
  have hd : 0 < (G.tr ^ 2 - 4 * G.nm).natAbs := Int.natAbs_pos.2 (ne_of_lt G.disc_neg)
  obtain ⟨p, hp, hpM, r, hr⟩ := schur G.tr G.nm (N * e * M * (G.tr ^ 2 - 4 * G.nm).natAbs) (by positivity)
  haveI : Fact p.Prime := ⟨hp⟩
  have hN' : ¬ p ∣ N := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _) _)
  have he' : ¬ p ∣ e := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _) _)
  have hM' : ¬ p ∣ M := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have hd' : ¬ (p : ℤ) ∣ G.tr ^ 2 - 4 * G.nm := fun h => hpM (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _)
  refine ⟨p, inferInstance,
    { F := G.F, fld := G.fld, nf := G.nf, cm := G.cm, bar := G.bar, bar_eq := G.bar_eq, ω := G.ω,
      tr := G.tr, nm := G.nm, tr_eq := G.tr_eq, nm_eq := G.nm_eq, disc_neg := G.disc_neg, disc_p := hd',
      split := ⟨r, hr⟩, O := G.O, rng := G.rng, alg := G.alg, freeO := G.freeO, finO := G.finO,
      m := G.m, m_pos := G.m_pos, rankO := G.rankO, central := G.central, star := G.star,
      star_star := G.star_star, star_F := G.star_F, splitP := hsplit p hM', La := G.La, acg := G.acg,
      modO := G.modO, freeLa := G.freeLa, finLa := G.finLa, n := G.n, n_pos := G.n_pos, rankLa := G.rankLa,
      EF := G.EF, alt := G.alt, nondeg := G.nondeg,
      perfP := ⟨e, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 he'), hperf⟩,
      adj := G.adj, a := G.a, ρc := G.ρc, ρc_root := G.ρc_root, tau := G.tau, tau_ω := G.tau_ω,
      dom := G.dom },
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hN'), rfl⟩

end GlobalTheory.GoodPrime
