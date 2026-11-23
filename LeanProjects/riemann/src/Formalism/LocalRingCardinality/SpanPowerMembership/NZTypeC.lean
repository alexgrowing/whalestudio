import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeB

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder

variable {g : ℕ} [hg : Fact g.Prime]

section One

variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)

include hd hu in
theorem finOrd (i : ℕ) : IsOfFinOrder ((u : Fbar g) ^ (g ^ i)) := by
  have h2 := one_lt_pow_g (g := g) hd
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨g ^ d - 1, by omega, ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]
  simp

include hd hu in
theorem no_prime_power {q0 ℓ : ℕ} (hℓ : ℓ.Prime) (hq0 : q0.Prime) (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1)
    (hqg : q0 ∣ g - 1) (i c : ℕ) : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) ≠ 1 := by
  intro h
  have h1 : u ^ (g ^ i * ℓ ^ c) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, pow_mul, h]; rfl)
  have h2 : g ^ d - 1 ∣ ℓ ^ c :=
    ((coprime_n d hd).pow_right i).dvd_of_dvd_mul_left (hu ▸ orderOf_dvd_of_pow_eq_one h1)
  have h3 : g - 1 ∣ g ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  have e1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).mp
    (Nat.prime_two.dvd_of_dvd_pow ((h2g.trans h3).trans h2))
  have e2 := (Nat.prime_dvd_prime_iff_eq hq0 hℓ).mp (hq0.dvd_of_dvd_pow ((hqg.trans h3).trans h2))
  exact hq2 (e2.trans e1.symm)

include hd hu in
theorem exc_same {ℓ : ℕ} (hℓ : ℓ.Prime) {i j c : ℕ} (hi : i < d) (hj : j < d) (hij : i ≠ j)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((u : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g d ℓ := by
  have key : ∀ {i j : ℕ}, i < j → j < d → u ^ (g ^ i * ℓ ^ c) = u ^ (g ^ j * ℓ ^ c) → Exc g d ℓ := by
    intro i j hij hj h
    refine exc_of_dvd (e := j - i) hg.out.two_le hℓ hd ?_ (dvd_of_pow_eq hd u hu hij.le h)
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left d (j - i)
    have h1 : Nat.gcd d (j - i) ≤ j - i := Nat.gcd_le_right _ (by omega)
    have h0 : 0 < Nat.gcd d (j - i) := Nat.gcd_pos_of_pos_left _ hd
    have ht2 : 2 ≤ t := by
      by_contra hlt
      interval_cases t
      · omega
      · omega
    calc 2 * Nat.gcd d (j - i) = Nat.gcd d (j - i) * 2 := mul_comm _ _
      _ ≤ Nat.gcd d (j - i) * t := Nat.mul_le_mul_left _ ht2
      _ = d := ht.symm
  have h' : u ^ (g ^ i * ℓ ^ c) = u ^ (g ^ j * ℓ ^ c) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, pow_mul, h])
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key h1 hj h'
  · exact key h1 hi h'.symm

end One

theorem exc_cross {p s ℓ : ℕ} (hℓ : ℓ.Prime) (hp : 2 ≤ p) (hs : 1 ≤ s) (hc : Nat.Coprime p s)
    (u w : (Fbar g)ˣ) (hu : orderOf u = g ^ p - 1) (hw : orderOf w = g ^ s - 1) (i j c : ℕ)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((w : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g p ℓ := by
  have h' : u ^ (g ^ i * ℓ ^ c) = w ^ (g ^ j * ℓ ^ c) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, pow_mul, h])
  have h1 : u ^ (g ^ i * (ℓ ^ c * (g ^ s - 1))) = 1 := by
    rw [← mul_assoc, pow_mul, h', ← pow_mul, mul_comm, pow_mul, ← hw, pow_orderOf_eq_one, one_pow]
  have h2 : g ^ p - 1 ∣ ℓ ^ c * (g ^ s - 1) :=
    ((coprime_n p (by omega)).pow_right i).dvd_of_dvd_mul_left (hu ▸ orderOf_dvd_of_pow_eq_one h1)
  exact exc_of_dvd hg.out.two_le hℓ (by omega) (by rw [hc]; omega) h2

structure LabelOK (N : ℕ) (f : (ZMod g)[X]) : Prop where
  monic : f.Monic
  deg : f.natDegree = N
  c0 : f.coeff 0 ≠ 0
  sqf : Squarefree f
  inj : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ BB N g → ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f,
    primeToPart ℓ x = primeToPart ℓ y → x = y
  ne1 : ∀ ℓ : ℕ, ℓ.Prime → ∀ x ∈ rootsBar f, primeToPart ℓ x ≠ primeToPart ℓ (1 : Fbar g)

theorem exists_labels (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB q : (ZMod g)[X], LabelOK N fA ∧ LabelOK N fB ∧
      (∀ r : (ZMod g)[X], r ∣ fA → r.natDegree ≠ 0 → N ≤ r.natDegree) ∧
      Irreducible q ∧ q ∣ fB ∧ q.natDegree = p := by
  have hN : 1 ≤ N := by omega
  set s := N - p with hs
  have hs1 : 1 ≤ s := by omega
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨uN, huN⟩ := exists_gen (g := g) N hN
  obtain ⟨up, hup⟩ := exists_gen (g := g) p hp1
  obtain ⟨us, hus⟩ := exists_gen (g := g) s hs1
  obtain ⟨PN, hPN, dN, mN⟩ := exists_orbP hN uN huN
  obtain ⟨Pp, hPp, dp, mp⟩ := exists_orbP hp1 up hup
  obtain ⟨Ps, hPs, ds, ms⟩ := exists_orbP hs1 us hus
  have iN := irreducible_P hN uN huN hPN dN
  have ip := irreducible_P hp1 up hup hPp dp
  have is := irreducible_P hs1 us hus hPs ds
  have one_fin : IsOfFinOrder (1 : Fbar g) := IsOfFinOrder.one
  have hcop : Nat.Coprime p s := (Nat.Prime.coprime_iff_not_dvd hp).mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have memB : ∀ y, y ∈ rootsBar (Pp * Ps) ↔ y ∈ rootsBar Pp ∨ y ∈ rootsBar Ps := fun y => by
    unfold rootsBar
    rw [Polynomial.map_mul, roots_mul (mul_ne_zero (by rw [hPp]; exact (orbQ_monic up).ne_zero)
      (by rw [hPs]; exact (orbQ_monic us).ne_zero)), Multiset.mem_add]
  refine ⟨PN, Pp * Ps, Pp, ⟨mN, dN, coeff_zero_P uN hPN, iN.squarefree, ?_, ?_⟩,
    ⟨mp.mul ms, by rw [mp.natDegree_mul ms, dp, ds]; omega, ?_, ?_, ?_, ?_⟩,
    fun r hr hr0 => le_natDegree_of_dvd hN uN huN hPN hr hr0, ip, Dvd.intro _ rfl, dp⟩
  · intro ℓ hℓ hBB x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P uN hPN).mp hx
    obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P uN hPN).mp hy
    obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hN uN huN i) (finOrd hN uN huN j) hxy
    by_contra hne
    exact hBB (Or.inr ⟨N, hN, le_rfl, exc_same hN uN huN hℓ hi hj (fun e => hne (by rw [e])) hc⟩)
  · intro ℓ hℓ x hx hxy
    obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P uN hPN).mp hx
    obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hN uN huN i) one_fin hxy
    exact no_prime_power hN uN huN hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])
  · rw [mul_coeff_zero]; exact mul_ne_zero (coeff_zero_P up hPp) (coeff_zero_P us hPs)
  · refine squarefree_mul_iff.mpr ⟨ip.isRelPrime_iff_not_dvd.mpr fun hdv => ?_, ip.squarefree, is.squarefree⟩
    have := natDegree_le_of_dvd hdv ms.ne_zero
    omega
  · intro ℓ hℓ hBB x hx y hy hxy
    have hBp : ¬ Exc g p ℓ := fun h => hBB (Or.inr ⟨p, hp1, by omega, h⟩)
    have hBs : ¬ Exc g s ℓ := fun h => hBB (Or.inr ⟨s, hs1, by omega, h⟩)
    rcases (memB x).mp hx with hx | hx <;> rcases (memB y).mp hy with hy | hy
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P up hPp).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) (finOrd hp1 up hup j) hxy
      by_contra hne
      exact hBp (exc_same hp1 up hup hℓ hi hj (fun e => hne (by rw [e])) hc)
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P us hPs).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) (finOrd hs1 us hus j) hxy
      exact (hBp (exc_cross hℓ hp.two_le hs1 hcop up us hup hus i j c hc)).elim
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P up hPp).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) (finOrd hp1 up hup j) hxy
      exact (hBp (exc_cross hℓ hp.two_le hs1 hcop up us hup hus j i c hc.symm)).elim
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P us hPs).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) (finOrd hs1 us hus j) hxy
      by_contra hne
      exact hBs (exc_same hs1 us hus hℓ hi hj (fun e => hne (by rw [e])) hc)
  · intro ℓ hℓ x hx hxy
    rcases (memB x).mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) one_fin hxy
      exact no_prime_power hp1 up hup hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) one_fin hxy
      exact no_prime_power hs1 us hus hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])

theorem exists_good (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB : (ZMod g)[X], fA ≠ fB ∧ (fA.Monic ∧ fA.natDegree = N ∧ fA.coeff 0 ≠ 0) ∧
      (fB.Monic ∧ fB.natDegree = N ∧ fB.coeff 0 ≠ 0) ∧
      ∀ (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
        IsGood N g (fun v => if t v then fA else fB) (fun (_ : PP) (_ : J) => (1 : (ZMod g)ˣ)) := by
  obtain ⟨fA, fB, q, hA, hB, hdiv, hq, hqB, hqd⟩ := exists_labels (g := g) N p q0 hp h1 h2 hq0 hq2 h2g hqg
  refine ⟨fA, fB, fun e => ?_, ⟨hA.monic, hA.deg, hA.c0⟩, ⟨hB.monic, hB.deg, hB.c0⟩,
    fun PP J t ⟨vA, hvA⟩ ⟨vB, hvB⟩ => ?_⟩
  · have := hdiv q (e ▸ hqB) (by rw [hqd]; exact hp.ne_zero)
    omega
  have hOK : ∀ v, LabelOK N (if t v then fA else fB) := fun v => by split_ifs <;> assumption
  refine ⟨fun v => ⟨(hOK v).monic, (hOK v).deg, (hOK v).c0⟩, fun v => (hOK v).sqf,
    fun ℓ hℓ hBB v => (hOK v).inj ℓ hℓ hBB, fun ℓ hℓ _ v _ x hx => ?_, fun a ha1 ha2 => ⟨vA, ?_⟩,
    ⟨vB, q, hq, ?_, hqd ▸ hp, by omega, by omega⟩⟩
  · rw [Units.val_one, map_one]; exact (hOK v).ne1 ℓ hℓ x hx
  · rintro ⟨r, hr, hra⟩
    simp only [hvA, if_true] at hr
    have := hdiv r hr (by omega)
    omega
  · simp only [hvB]; exact hqB

end Formalism.BasicNotions.Examples₂.NZ
