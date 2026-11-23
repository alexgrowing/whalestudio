import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.HeckeRel

variable {k N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℕ → ℂ}

theorem eig_at (h : Prim k N χ g) {q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N) (n : ℕ) :
    g (q * n) = g q * g n - χ q * (q : ℂ) ^ (k - 1) * (if q ∣ n then g (n / q) else 0) := by
  have := congrFun (h.eig q hq hqN) n
  simp only [To, Vo, ch, Int.cast_natCast] at this
  linear_combination this

theorem pow_rec (h : Prim k N χ g) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (r : ℕ) :
    g (p ^ (r + 2)) = g p * g (p ^ (r + 1)) - χ p * (p : ℂ) ^ (k - 1) * g (p ^ r) := by
  have e := eig_at h hp hpN (p ^ (r + 1))
  rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero r)), pow_succ' p r,
    Nat.mul_div_cancel_left _ hp.pos, ← pow_succ', ← pow_succ'] at e
  exact e

theorem ppow_mul (h : Prim k N χ g) {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n) (r : ℕ) :
    g (p ^ r * n) = g (p ^ r) * g n := by
  by_cases hpN : p ∣ N
  · rcases r with _ | r
    · simp [h.one]
    · have h1 : g (p ^ (r + 1) * n) = 0 := h.zero _ (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
        (dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero r)) n) hpN)
      have h2 : g (p ^ (r + 1)) = 0 := h.zero _ (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
        (dvd_pow_self p (Nat.succ_ne_zero r)) hpN)
      rw [h1, h2, zero_mul]
  · suffices H : ∀ r, g (p ^ r * n) = g (p ^ r) * g n ∧ g (p ^ (r + 1) * n) = g (p ^ (r + 1)) * g n from (H r).1
    intro r
    induction r with
    | zero =>
      refine ⟨by simp [h.one], ?_⟩
      rw [zero_add, pow_one, eig_at h hp hpN n, if_neg hn, mul_zero, sub_zero]
    | succ r ih =>
      refine ⟨ih.2, ?_⟩
      have hd : p ∣ p ^ (r + 1) * n := dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero r)) n
      have e := eig_at h hp hpN (p ^ (r + 1) * n)
      have hq : p ^ (r + 1) * n / p = p ^ r * n := by
        rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      have hy : p ^ (r + 1 + 1) * n = p * (p ^ (r + 1) * n) := by ring
      rw [if_pos hd, hq] at e
      rw [hy, e, pow_rec h hp hpN r, ih.1, ih.2]
      ring

theorem mul_coprime (h : Prim k N χ g) : ∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n hmn
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [Nat.coprime_zero_left] at hmn
      subst hmn; simp [h.one]
    · simp [h.one]
  · have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
    have hpm0 : m.minFac ∣ m := Nat.minFac_dvd _
    generalize m.minFac = p at hp hpm0
    obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hp.ne_one
    have hpm : p ∣ p ^ e * m' := hpm0
    have he : e ≠ 0 := by
      rintro rfl
      simp only [pow_zero, one_mul] at hpm
      exact hm' hpm
    have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    have hlt : m' < p ^ e * m' := by
      have : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow he p)
      nlinarith
    have hpn : ¬ p ∣ n := fun hd => Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpm hd hmn
    have hcop : m'.Coprime n := Nat.Coprime.coprime_dvd_left (dvd_mul_left m' _) hmn
    rw [mul_assoc, ppow_mul h hp (fun hd => (Nat.Prime.dvd_mul hp).1 hd |>.elim hm' hpn),
      ih m' hlt n hcop, ppow_mul h hp hm']
    ring

end GlobalTheory.EisM.HeckeRel

namespace GlobalTheory.EisM.HeckeRel

variable {k N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℕ → ℂ}

theorem depletedCuspEigenform_primePow_mul_shift (h : Prim k N χ g) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∀ a d : ℕ, g (p ^ a) * g (p ^ (a + d)) =
      ∑ i ∈ Finset.range (a + 1), (χ p * (p : ℂ) ^ (k - 1)) ^ i * g (p ^ (2 * a + d - 2 * i)) := by
  set F : ℂ := χ p * (p : ℂ) ^ (k - 1) with hF
  have hrec : ∀ e : ℕ, g p * g (p ^ (e + 1)) = g (p ^ (e + 2)) + F * g (p ^ e) := by
    intro e; rw [pow_rec h hp hpN e]; ring
  suffices H : ∀ a, (∀ d, g (p ^ a) * g (p ^ (a + d)) =
      ∑ i ∈ Finset.range (a + 1), F ^ i * g (p ^ (2 * a + d - 2 * i))) ∧
      (∀ d, g (p ^ (a + 1)) * g (p ^ (a + 1 + d)) =
      ∑ i ∈ Finset.range (a + 1 + 1), F ^ i * g (p ^ (2 * (a + 1) + d - 2 * i))) from fun a => (H a).1
  intro a
  induction a with
  | zero =>
    refine ⟨fun d => by simp [h.one], fun d => ?_⟩
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have e1 : 2 * (0 + 1) + d - 2 * 0 = d + 2 := by omega
    have e2 : 2 * (0 + 1) + d - 2 * 1 = d := by omega
    have e3 : 0 + 1 + d = d + 1 := by omega
    rw [e1, e2, e3, zero_add, pow_one, hrec d]
    simp
  | succ a ih =>
    refine ⟨ih.2, fun d => ?_⟩
    have hl : g (p ^ (a + 1 + 1)) * g (p ^ (a + 1 + 1 + d)) =
        g p * (g (p ^ (a + 1)) * g (p ^ (a + 1 + (d + 1)))) - F * (g (p ^ a) * g (p ^ (a + (d + 2)))) := by
      have e1 : a + 1 + 1 + d = a + 1 + (d + 1) := by omega
      have e2 : a + 1 + 1 + d = a + (d + 2) := by omega
      rw [pow_rec h hp hpN a]
      rw [show a + 1 + 1 + d = a + 1 + (d + 1) by omega]
      rw [show a + 1 + (d + 1) = a + (d + 2) by omega]
      ring
    rw [hl, ih.2 (d + 1), ih.1 (d + 2), Finset.mul_sum, Finset.mul_sum]
    have key : ∀ i ∈ Finset.range (a + 1 + 1), g p * (F ^ i * g (p ^ (2 * (a + 1) + (d + 1) - 2 * i))) =
        F ^ i * g (p ^ (2 * (a + 1 + 1) + d - 2 * i)) + F * (F ^ i * g (p ^ (2 * a + (d + 2) - 2 * i))) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [show 2 * (a + 1) + (d + 1) - 2 * i = (2 * a + (d + 2) - 2 * i) + 1 by omega,
        show 2 * (a + 1 + 1) + d - 2 * i = (2 * a + (d + 2) - 2 * i) + 2 by omega]
      linear_combination (F ^ i) * hrec (2 * a + (d + 2) - 2 * i)
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_range_succ (n := a + 1 + 1),
      Finset.sum_range_succ (fun i => F * (F ^ i * g (p ^ (2 * a + (d + 2) - 2 * i)))) (a + 1)]
    rw [show 2 * (a + 1 + 1) + d - 2 * (a + 1 + 1) = d by omega, show 2 * a + (d + 2) - 2 * (a + 1) = d by omega]
    ring

theorem pp (h : Prim k N χ g) : ∀ p a b : ℕ, p.Prime → g (p ^ a) * g (p ^ b) = ∑ i ∈ Finset.range (min a b + 1), χ ((p ^ i : ℕ) : ZMod N) * ((p ^ i : ℕ) : ℂ) ^ (k - 1) * g (p ^ (a + b - 2 * i)) := by
  intro p a b hp
  by_cases hpN : p ∣ N
  · have hz : ∀ e, e ≠ 0 → g (p ^ e) = 0 := fun e he =>
      h.zero _ (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p he) hpN)
    have hχ : ∀ i, i ≠ 0 → χ ((p ^ i : ℕ) : ZMod N) = 0 := by
      intro i hi
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p hi) hpN
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [h.one]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [h.one]
    rw [hz a ha.ne', zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hz (a + b - 2 * 0) (by omega), mul_zero]
    · rw [hχ i hi.ne', zero_mul, zero_mul]
  · have hF : ∀ i, χ ((p ^ i : ℕ) : ZMod N) * ((p ^ i : ℕ) : ℂ) ^ (k - 1) = (χ p * (p : ℂ) ^ (k - 1)) ^ i := by
      intro i
      rw [Nat.cast_pow, Nat.cast_pow, map_pow, ← pow_mul, mul_comm i, pow_mul, mul_pow]
    simp only [hF]
    rcases le_total a b with hab | hab
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [min_eq_left hab, depletedCuspEigenform_primePow_mul_shift h hp hpN a d]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show a + (a + d) - 2 * i = 2 * a + d - 2 * i by omega]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [min_eq_right hab, mul_comm, depletedCuspEigenform_primePow_mul_shift h hp hpN b d]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show b + d + b - 2 * i = 2 * b + d - 2 * i by omega]

end GlobalTheory.EisM.HeckeRel

namespace GlobalTheory.EisM.HeckeRel

theorem gcd_pow_mul {p a b m' n' : ℕ} (hp : p.Prime) (hm' : ¬ p ∣ m') (hn' : ¬ p ∣ n') :
    Nat.gcd (p ^ a * m') (p ^ b * n') = p ^ min a b * Nat.gcd m' n' := by
  have cop : ∀ e x, ¬ p ∣ x → (p ^ e).Coprime x := fun e x hx =>
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hx)
  rw [Nat.Coprime.gcd_mul _ (cop b n' hn'), Nat.gcd_comm (p ^ a * m') (p ^ b),
    Nat.Coprime.gcd_mul _ (cop a m' hm'), Nat.gcd_comm (p ^ a * m') n',
    Nat.Coprime.gcd_mul _ (cop a m' hm'), Nat.Coprime.gcd_eq_one (cop b m' hm'),
    Nat.Coprime.gcd_eq_one (cop a n' hn').symm, Nat.gcd_comm n' m', mul_one, one_mul]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, Nat.gcd_eq_right (Nat.pow_dvd_pow p hab)]
  · rw [min_eq_right hab, Nat.gcd_eq_left (Nat.pow_dvd_pow p hab)]

theorem sum_divisors_mul_coprime {A B : ℕ} (hAB : A.Coprime B) (F : ℕ → ℂ) :
    ∑ x ∈ (A * B).divisors, F x = ∑ x ∈ A.divisors, ∑ y ∈ B.divisors, F (x * y) := by
  rw [Nat.Coprime.divisors_mul hAB, Finset.sum_map]
  exact (Finset.sum_attach _ (fun q : ℕ × ℕ => F (q.1 * q.2))).trans (Finset.sum_product _ _ _)

theorem gen (f g : ℕ → ℂ) (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hg : ∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n)
    (hpp : ∀ p a b : ℕ, p.Prime → g (p ^ a) * g (p ^ b) =
      ∑ i ∈ Finset.range (min a b + 1), f (p ^ i) * g (p ^ (a + b - 2 * i))) :
    ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, f δ * g (m * n / δ ^ 2) := by
  suffices H : ∀ s m n, m * n = s → 0 < m → 0 < n →
      g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, f δ * g (m * n / δ ^ 2) from
    fun m n hm hn => H _ m n rfl hm hn
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro m n hs hm hn
  by_cases h1 : m * n = 1
  · have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_left h1
    subst hm1 hn1
    have := hpp 2 0 0 Nat.prime_two
    simpa using this
  have hp : (m * n).minFac.Prime := Nat.minFac_prime h1
  have hpd : (m * n).minFac ∣ m * n := Nat.minFac_dvd _
  generalize (m * n).minFac = p at hp hpd
  obtain ⟨a, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
  obtain ⟨b, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hn'0 : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hpmn : ¬ p ∣ m' * n' := fun hd => (hp.dvd_mul.1 hd).elim hm' hn'
  have hab : a + b ≠ 0 := by
    intro hab
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    simp only [pow_zero, one_mul] at hpd
    exact hpmn hpd
  have hmn : p ^ a * m' * (p ^ b * n') = p ^ (a + b) * (m' * n') := by ring
  have hlt : m' * n' < s := by
    rw [← hs, hmn]
    have h2 : 2 ≤ p ^ (a + b) := le_trans hp.two_le (Nat.le_self_pow hab p)
    have h3 : 0 < m' * n' := Nat.mul_pos hm'0 hn'0
    nlinarith
  have IH := ih _ hlt m' n' rfl hm'0 hn'0
  have cop : ∀ e x, ¬ p ∣ x → (p ^ e).Coprime x := fun e x hx =>
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hx)
  have hGp : ¬ p ∣ Nat.gcd m' n' := fun hd => hm' (hd.trans (Nat.gcd_dvd_left _ _))
  rw [hg _ _ (cop a m' hm'), hg _ _ (cop b n' hn'), gcd_pow_mul hp hm' hn',
    sum_divisors_mul_coprime (cop _ _ hGp), Nat.sum_divisors_prime_pow hp]
  have e1 : g (p ^ a) * g m' * (g (p ^ b) * g n') = (g (p ^ a) * g (p ^ b)) * (g m' * g n') := by ring
  rw [e1, hpp p a b hp, IH, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun y hy => ?_
  have hi' : i ≤ min a b := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hyG : y ∣ Nat.gcd m' n' := Nat.dvd_of_mem_divisors hy
  obtain ⟨u, hu⟩ := hyG.trans (Nat.gcd_dvd_left m' n')
  obtain ⟨v, hv⟩ := hyG.trans (Nat.gcd_dvd_right m' n')
  have hy0 : 0 < y := Nat.pos_of_mem_divisors hy
  have hq1 : m' * n' / y ^ 2 = u * v := by
    rw [hu, hv, show y * u * (y * v) = y ^ 2 * (u * v) by ring, Nat.mul_div_cancel_left _ (by positivity)]
  have hq2 : p ^ a * m' * (p ^ b * n') / (p ^ i * y) ^ 2 = p ^ (a + b - 2 * i) * (u * v) := by
    have hexp : p ^ (a + b) = p ^ (2 * i) * p ^ (a + b - 2 * i) := by
      rw [← pow_add]; congr 1; omega
    rw [hmn, hexp, hu, hv, show p ^ (2 * i) * p ^ (a + b - 2 * i) * (y * u * (y * v)) =
      (p ^ i * y) ^ 2 * (p ^ (a + b - 2 * i) * (u * v)) by ring,
      Nat.mul_div_cancel_left _ (by have := hp.pos; positivity)]
  have huv : ¬ p ∣ u * v := fun hd => hpmn (hd.trans ⟨y * y, by rw [hu, hv]; ring⟩)
  rw [hq1, hq2, hf, hg _ _ (cop _ _ huv)]
  ring

end GlobalTheory.EisM.HeckeRel

theorem GlobalTheory.EisM.hecke_relations : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g → (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) ∧ (∀ p r : ℕ, p.Prime → ¬ p ∣ N → g (p ^ (r + 2)) = g p * g (p ^ (r + 1)) - χ p * (p : ℂ) ^ (k - 1) * g (p ^ r)) ∧ ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (k - 1) * g (m * n / δ ^ 2) := by
  intro k N χ g _ _ h
  refine ⟨GlobalTheory.EisM.HeckeRel.mul_coprime h, fun p r hp hpN => GlobalTheory.EisM.HeckeRel.pow_rec h hp hpN r, ?_⟩
  refine GlobalTheory.EisM.HeckeRel.gen (fun δ : ℕ => χ δ * (δ : ℂ) ^ (k - 1)) g ?_ (GlobalTheory.EisM.HeckeRel.mul_coprime h) ?_
  · intro a b
    simp only [Nat.cast_mul, map_mul, mul_pow]
    ring
  · intro p a b hp
    exact GlobalTheory.EisM.HeckeRel.pp h p a b hp

end
