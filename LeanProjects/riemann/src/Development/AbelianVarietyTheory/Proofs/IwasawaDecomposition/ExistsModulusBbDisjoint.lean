import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

namespace GlobalTheory.Mem

theorem exc_dvd_prod_range {g e l r : ℕ} (hg : 1 ≤ g) (h1 : 1 ≤ e) (hr : e ≤ r) (h : Formalism.CyclotomicNorms.Exc g e l) :
    l ∣ ∏ i ∈ Finset.range r, (g ^ (i + 1) - 1) := by
  have hv : padicValNat l (g ^ e - 1) ≠ 0 := by
    intro h0
    have h2 := h.2
    rw [h0, mul_zero, pow_zero] at h2
    have := Nat.one_le_pow e g hg
    omega
  have h3 : g ^ e - 1 ∣ ∏ i ∈ Finset.range r, (g ^ (i + 1) - 1) := by
    have := Finset.dvd_prod_of_mem (fun i => g ^ (i + 1) - 1) (Finset.mem_range.2 (show e - 1 < r by omega))
    rwa [Nat.sub_add_cancel h1] at this
  exact ((dvd_pow_self l hv).trans pow_padicValNat_dvd).trans h3

theorem not_exc_of_cong_sq {M l g e c k : ℕ} (hl : l.Prime) (hM : l ^ k ∣ M) (hM0 : 0 < M)
    (hg : g = 1 + 2 * M + M ^ 2 * c) (hbig : M ^ 8 ≤ g) (h1 : 1 ≤ e) (hk : 2 * e < l ^ k) :
    ¬ Formalism.CyclotomicNorms.Exc g e l := by
  rintro ⟨-, hlt⟩
  have : Fact l.Prime := ⟨hl⟩
  set x : ℕ := M * (2 + M * c) with hx
  have hgx : g = x + 1 := by rw [hg, hx]; ring
  set S : ℕ := ∑ i ∈ Finset.range e, (x + 1) ^ i with hS
  have hgeo : S * x + 1 = g ^ e := by rw [hgx]; exact geom_sum_mul_add x e
  have hSe : S * (2 + M * c) ≡ 2 * e [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [hS, hx]
    push_cast
    simp [mul_comm]
  have hnd : ¬ l ^ k ∣ S * (2 + M * c) := by
    intro hd
    have := Nat.le_of_dvd (by omega) ((hSe.dvd_iff hM).1 hd)
    omega
  have hS0 : S * (2 + M * c) ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero _)
  have hvS : padicValNat l (S * (2 + M * c)) ≤ k := by
    by_contra hc
    exact hnd ((pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd)
  have hval : padicValNat l (g ^ e - 1) = padicValNat l (S * (2 + M * c)) + padicValNat l M := by
    have : S * x = S * (2 + M * c) * M := by rw [hx]; ring
    rw [← hgeo, Nat.add_sub_cancel, this, padicValNat.mul hS0 hM0.ne']
  have hle : l ^ (4 * padicValNat l (g ^ e - 1)) ≤ M ^ 8 := by
    have a1 : l ^ padicValNat l M ≤ M := Nat.le_of_dvd hM0 pow_padicValNat_dvd
    have a2 : l ^ k ≤ M := Nat.le_of_dvd hM0 hM
    calc l ^ (4 * padicValNat l (g ^ e - 1)) ≤ l ^ (k * 4 + padicValNat l M * 4) :=
          Nat.pow_le_pow_right hl.pos (by rw [hval]; omega)
      _ = (l ^ k) ^ 4 * (l ^ padicValNat l M) ^ 4 := by rw [pow_add, ← pow_mul, ← pow_mul]
      _ ≤ M ^ 4 * M ^ 4 := Nat.mul_le_mul (Nat.pow_le_pow_left a2 4) (Nat.pow_le_pow_left a1 4)
      _ = M ^ 8 := by ring
  have hge : g ≤ g ^ e := Nat.le_self_pow (by omega) g
  omega

theorem exists_modulus_bb_disjoint : ∀ (r g0 m : ℕ), g0.Prime → m ≠ 0 → ∃ M N : ℕ, M ≠ 0 ∧ m ∣ M ∧
    ∀ g1 : ℕ, g1.Prime → N < g1 → g1 ≡ (1 + M) ^ 2 [MOD M ^ 2] →
      Disjoint (Formalism.CyclotomicNorms.BB r g0) (Formalism.CyclotomicNorms.BB r g1) := by
  intro r g0 m hg0 hm
  set P : ℕ := g0 * ∏ i ∈ Finset.range r, (g0 ^ (i + 1) - 1) with hP
  have hP0 : 0 < P := by
    refine Nat.mul_pos hg0.pos (Finset.prod_pos fun i _ => ?_)
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero i) hg0.one_lt)
  set M : ℕ := (m * P) ^ (2 * r + 1) with hM
  have hmP : 0 < m * P := Nat.mul_pos (Nat.pos_of_ne_zero hm) hP0
  have hM0 : 0 < M := pow_pos hmP _
  have hmM : m ∣ M := (Dvd.intro P rfl).trans (dvd_pow_self _ (by omega))
  refine ⟨M, M ^ 8 + 1 + 2 * M + P, hM0.ne', hmM, fun g1 _ hgt hmod => ?_⟩
  have hmod' : 1 + 2 * M ≡ g1 [MOD M ^ 2] := by
    refine Nat.ModEq.trans ?_ hmod.symm
    have : (1 + M) ^ 2 = 1 + 2 * M + M ^ 2 := by ring
    rw [this]
    exact (Nat.add_modEq_right).symm
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' (show 1 + 2 * M ≤ g1 by omega)).1 hmod'
  have hg1 : g1 = 1 + 2 * M + M ^ 2 * c := by omega
  have hbig : M ^ 8 ≤ g1 := by omega
  rw [Set.disjoint_left]
  intro l hl0 hl1
  have hlP : l.Prime ∧ l ∣ P := by
    rcases hl0 with h | ⟨e, h1, h9, h⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨hg0, Dvd.intro _ rfl⟩
    · exact ⟨h.1, (exc_dvd_prod_range hg0.pos h1 h9 h).trans (Dvd.intro_left _ rfl)⟩
  rcases hl1 with h | ⟨e, h1, h9, h⟩
  · have := Nat.le_of_dvd hP0 hlP.2
    rw [Set.mem_singleton_iff.1 h] at this
    omega
  · have hk : 2 * r + 1 < l ^ (2 * r + 1) := Nat.lt_pow_self hlP.1.one_lt
    exact not_exc_of_cong_sq hlP.1 (pow_dvd_pow_of_dvd (hlP.2.trans (Dvd.intro_left _ rfl)) (2 * r + 1)) hM0 hg1
      hbig h1 (by omega) h

end GlobalTheory.Mem
