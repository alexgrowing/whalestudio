import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.QuadSubfield GlobalTheory.PlaceComponents

namespace GlobalTheory.IntegralAtBothPrimes

theorem den_coprime_of_norm_le_one {p : ℕ} [hp : Fact p.Prime] (q : ℚ) (h : ‖(q : ℂ_[p])‖ ≤ 1) :
    Nat.Coprime q.den p := by
  have h1 : ‖(q : ℚ_[p])‖ ≤ 1 := by
    have := norm_algebraMap' ℂ_[p] (q : ℚ_[p])
    rw [map_ratCast] at this
    rwa [← this]
  rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
  intro hd
  have h2 : ‖((q.den : ℤ) : ℚ_[p])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
  have h3 : ((q.num : ℤ) : ℚ_[p]) = (q : ℚ_[p]) * ((q.den : ℤ) : ℚ_[p]) := by
    rw [Int.cast_natCast]
    exact_mod_cast (congrArg (fun x : ℚ => (x : ℚ_[p])) (Rat.mul_den_eq_num q)).symm
  have h4 : ‖((q.num : ℤ) : ℚ_[p])‖ < 1 := by
    rw [h3, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h1 (norm_nonneg _) h2
  have h5 : p ∣ q.num.natAbs := Int.natCast_dvd.1 (Padic.norm_intCast_lt_one_iff.1 h4)
  exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes q.reduced h5 hd)

theorem isIntegral_of_quadratic {K : Type*} [CommRing K] (x : K) (a b : ℤ)
    (h : x ^ 2 - (a : K) * x + (b : K) = 0) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b, by monicity!, ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
  exact h

theorem exists_coprime_mul_integral (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : D.host.K)
    (h1 : ‖atP D lam c‖ ≤ 1) (h2 : ‖atPbar D lam c‖ ≤ 1) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ z : 𝓞 D.host.K, (s : D.host.K) * c = (z : D.host.K) := by
  rw [atP₂] at h1
  rw [atPbar_eq, ← homP_conjK] at h2
  obtain ⟨t, n, ht, hn⟩ := exists_trace_norm D c
  have ht1 : ‖(t : ℂ_[p])‖ ≤ 1 := by
    have := congrArg (homP D lam) ht
    rw [map_add, map_ratCast] at this
    rw [← this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  have hn1 : ‖(n : ℂ_[p])‖ ≤ 1 := by
    have := congrArg (homP D lam) hn
    rw [map_mul, map_ratCast] at this
    rw [← this, norm_mul]
    exact mul_le_one₀ h1 (norm_nonneg _) h2
  refine ⟨t.den * n.den, Nat.Coprime.mul_left (den_coprime_of_norm_le_one t ht1) (den_coprime_of_norm_le_one n hn1), ?_⟩
  have et : (t : D.host.K) * (t.den : D.host.K) = (t.num : D.host.K) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : D.host.K)) (Rat.mul_den_eq_num t)
  have en : (n : D.host.K) * (n.den : D.host.K) = (n.num : D.host.K) := by
    exact_mod_cast congrArg (fun x : ℚ => (x : D.host.K)) (Rat.mul_den_eq_num n)
  have hi : IsIntegral ℤ (((t.den * n.den : ℕ) : D.host.K) * c) := by
    refine isIntegral_of_quadratic _ (t.num * n.den) (t.den ^ 2 * n.den * n.num) ?_
    push_cast
    rw [← et, ← en, ← ht, ← hn]
    ring
  exact ⟨⟨_, hi⟩, rfl⟩

end GlobalTheory.IntegralAtBothPrimes
