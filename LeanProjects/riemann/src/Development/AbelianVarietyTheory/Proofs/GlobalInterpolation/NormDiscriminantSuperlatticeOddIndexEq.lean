import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeierstrassPSuperlatticeHalfPeriodProdStatement

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomDisc

theorem deriv_half (P : PeriodPair) {w : ℂ} (h : 2 * w ∈ P.lattice) : P.derivWeierstrassP w = 0 := by
  have h1 : P.derivWeierstrassP (w - 2 * w) = P.derivWeierstrassP w :=
    P.derivWeierstrassP_sub_coe w ⟨2 * w, h⟩
  rw [show w - 2 * w = -w by ring, P.derivWeierstrassP_neg] at h1
  linear_combination -h1 / 2

theorem cubic_root (P : PeriodPair) {w : ℂ} (h2 : 2 * w ∈ P.lattice) (hw : w ∉ P.lattice) :
    4 * P.weierstrassP w ^ 3 - P.g₂ * P.weierstrassP w - P.g₃ = 0 := by
  rw [← P.derivWeierstrassP_sq w hw, deriv_half P h2]
  ring

theorem disc_of_roots {g2 g3 a b c : ℂ} (ha : 4 * a ^ 3 - g2 * a - g3 = 0) (hb : 4 * b ^ 3 - g2 * b - g3 = 0)
    (hc : 4 * c ^ 3 - g2 * c - g3 = 0) (hab : a - b ≠ 0) (hac : a - c ≠ 0) (hbc : b - c ≠ 0) :
    g2 ^ 3 - 27 * g3 ^ 2 = 16 * ((a - b) * (a - c) * (b - c)) ^ 2 := by
  have e1 : 4 * (a ^ 2 + a * b + b ^ 2) = g2 := by
    have h : (a - b) * (4 * (a ^ 2 + a * b + b ^ 2) - g2) = 0 := by linear_combination ha - hb
    linear_combination (mul_eq_zero.mp h).resolve_left hab
  have e2 : 4 * (a ^ 2 + a * c + c ^ 2) = g2 := by
    have h : (a - c) * (4 * (a ^ 2 + a * c + c ^ 2) - g2) = 0 := by linear_combination ha - hc
    linear_combination (mul_eq_zero.mp h).resolve_left hac
  have hs : a + b + c = 0 := by
    have h : (b - c) * (a + b + c) = 0 := by linear_combination (e1 - e2) / 4
    exact (mul_eq_zero.mp h).resolve_left hbc
  have hc' : c = -a - b := by linear_combination hs
  have hg3 : g3 = 4 * a ^ 3 - g2 * a := by linear_combination -ha
  rw [hg3, ← e1, hc']
  ring

theorem exists_reps (L L' : PeriodPair) (N : ℕ) (hN0 : N ≠ 0) (hLL : L.lattice ≤ L'.lattice)
    (hN : ∀ x ∈ L'.lattice, (N : ℂ) * x ∈ L.lattice) :
    ∃ T : Finset ℂ, (∀ t ∈ T, t ∈ L'.lattice ∧ t ∉ L.lattice) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L.lattice → t = t') ∧
      ∀ x ∈ L'.lattice, x ∈ L.lattice ∨ ∃ t ∈ T, x - t ∈ L.lattice := by
  classical
  have hNz : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  let F : Finset ℂ := ((Finset.Ico (0 : ℤ) N) ×ˢ (Finset.Ico (0 : ℤ) N)).image
    (fun ij : ℤ × ℤ => ((ij.1 : ℂ) * L.ω₁ + (ij.2 : ℂ) * L.ω₂) / N)
  have hF : ∀ x ∈ L'.lattice, ∃ f ∈ F, x - f ∈ L.lattice := by
    intro x hx
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hN x hx)
    refine ⟨(((a % (N : ℤ) : ℤ) : ℂ) * L.ω₁ + ((b % (N : ℤ) : ℤ) : ℂ) * L.ω₂) / N, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨(a % (N : ℤ), b % (N : ℤ)), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_Ico]
      exact ⟨⟨Int.emod_nonneg _ hNz.ne', Int.emod_lt_of_pos _ hNz⟩,
        ⟨Int.emod_nonneg _ hNz.ne', Int.emod_lt_of_pos _ hNz⟩⟩
    · refine PeriodPair.mem_lattice.mpr ⟨a / (N : ℤ), b / (N : ℤ), ?_⟩
      have ea : (a : ℂ) = (N : ℂ) * ((a / (N : ℤ) : ℤ) : ℂ) + ((a % (N : ℤ) : ℤ) : ℂ) := by
        have h := Int.ediv_mul_add_emod a N
        exact_mod_cast (by linear_combination -h : a = (N : ℤ) * (a / (N : ℤ)) + a % (N : ℤ))
      have eb : (b : ℂ) = (N : ℂ) * ((b / (N : ℤ) : ℤ) : ℂ) + ((b % (N : ℤ) : ℤ) : ℂ) := by
        have h := Int.ediv_mul_add_emod b N
        exact_mod_cast (by linear_combination -h : b = (N : ℤ) * (b / (N : ℤ)) + b % (N : ℤ))
      have hx' : x = ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / N :=
        eq_div_of_mul_eq hNc (by rw [hab]; ring)
      rw [hx', ea, eb, div_sub_div_same, eq_div_iff hNc]
      ring
  let S := L.lattice.toAddSubgroup
  let r : ℂ → ℂ := fun f => Quotient.out (QuotientAddGroup.mk f : ℂ ⧸ S)
  have hr : ∀ f, f - r f ∈ L.lattice := by
    intro f
    have e : (QuotientAddGroup.mk (r f) : ℂ ⧸ S) = QuotientAddGroup.mk f := Quotient.out_eq _
    have h : -(r f) + f ∈ L.lattice := QuotientAddGroup.eq.mp e
    convert h using 1; ring
  have hr2 : ∀ f g, f - g ∈ L.lattice → r f = r g := by
    intro f g h
    have e : (QuotientAddGroup.mk f : ℂ ⧸ S) = QuotientAddGroup.mk g := by
      apply QuotientAddGroup.eq.mpr
      have h' : -f + g ∈ L.lattice := by convert neg_mem h using 1; ring
      exact h'
    exact congrArg Quotient.out e
  refine ⟨(F.filter (fun f => f ∈ L'.lattice ∧ f ∉ L.lattice)).image r, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨-, hf1, hf2⟩ := Finset.mem_filter.mp hf
    refine ⟨?_, ?_⟩
    · have h := sub_mem hf1 (hLL (hr f))
      convert h using 1; ring
    · intro h
      apply hf2
      have h' := add_mem (hr f) h
      convert h' using 1; ring
  · intro t ht t' ht' h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp ht'
    apply hr2
    have h' := add_mem (add_mem (hr f) h) (neg_mem (hr g))
    convert h' using 1; ring
  · intro x hx
    by_cases hxL : x ∈ L.lattice
    · exact Or.inl hxL
    · right
      obtain ⟨f, hfF, hxf⟩ := hF x hx
      refine ⟨r f, Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hfF, ?_, ?_⟩, rfl⟩, ?_⟩
      · have h := sub_mem hx (hLL hxf)
        convert h using 1; ring
      · intro hf
        apply hxL
        have h := add_mem hxf hf
        convert h using 1; ring
      · have h := add_mem hxf (hr f)
        convert h using 1; ring

variable {q : ℕ} [Fact q.Prime]

theorem dist_eq (M : Mdl q) (hOk : M.Ok) {n : ℕ} (hc : Nat.Coprime n q) {p p' : ℂ}
    (hp : (n : ℂ) * p ∈ M.L.lattice) (hp' : (n : ℂ) * p' ∈ M.L.lattice) (h1 : p ∉ M.L.lattice)
    (h2 : p' ∉ M.L.lattice) (h3 : p + p' ∉ M.L.lattice) (h4 : p - p' ∉ M.L.lattice) :
    ‖M.ι (M.L.weierstrassP p - M.L.weierstrassP p')‖ = ‖M.ι (M.c ^ 2)‖ := by
  have hc0 : M.c ≠ 0 := by
    have h := hOk
    unfold GlobalTheory.MomOne.Mdl.Ok at h
    exact h.1
  have hxd := (GlobalTheory.MomOne.TorsionReduction.torsion_integral_and_distinct q M n hOk hc).2
    p p' hp hp' h1 h2 h3 h4
  have hne : ‖M.ι (M.c ^ 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((map_ne_zero M.ι).mpr (pow_ne_zero 2 hc0))
  have e : M.ι (M.x p) - M.ι (M.x p') =
      M.ι (M.L.weierstrassP p - M.L.weierstrassP p') / M.ι (M.c ^ 2) := by
    rw [← map_sub, ← map_div₀]
    congr 1
    unfold GlobalTheory.MomOne.Mdl.x
    ring
  rw [e, norm_div, div_eq_one_iff_eq hne] at hxd
  exact hxd

theorem key (M : Mdl q) (L' : PeriodPair) (N : ℕ) (hOk : M.Ok) (hc : Nat.Coprime (2 * N) q)
    (hLL : M.L.lattice ≤ L'.lattice) (hN : ∀ x ∈ L'.lattice, (N : ℂ) * x ∈ M.L.lattice)
    (T : Finset ℂ) (T1 : ∀ t ∈ T, t ∈ L'.lattice ∧ t ∉ M.L.lattice)
    (T2 : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ M.L.lattice → t = t')
    (T3 : ∀ x ∈ L'.lattice, x ∈ M.L.lattice ∨ ∃ t ∈ T, x - t ∈ M.L.lattice)
    {w w' : ℂ} (hw2 : 2 * w ∈ M.L.lattice) (hw'2 : 2 * w' ∈ M.L.lattice) (hw : w ∉ L'.lattice)
    (hw' : w' ∉ L'.lattice) (hd : w - w' ∉ L'.lattice) :
    ‖M.ι (L'.weierstrassP w' - L'.weierstrassP w)‖ = ‖M.ι (M.c ^ 2)‖ ∧
      ‖M.ι (M.L.weierstrassP w' - M.L.weierstrassP w)‖ = ‖M.ι (M.c ^ 2)‖ := by
  have hc0 : M.c ≠ 0 := by
    have h := hOk
    unfold GlobalTheory.MomOne.Mdl.Ok at h
    exact h.1
  have hγ : ‖M.ι (M.c ^ 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((map_ne_zero M.ι).mpr (pow_ne_zero 2 hc0))
  have hp : ((2 * N : ℕ) : ℂ) * w' ∈ M.L.lattice := by
    have h := hN _ (hLL hw'2)
    convert h using 1; push_cast; ring
  have hpw : ((2 * N : ℕ) : ℂ) * w ∈ M.L.lattice := by
    have h := hN _ (hLL hw2)
    convert h using 1; push_cast; ring
  have hw'L : w' ∉ M.L.lattice := fun h => hw' (hLL h)
  have hwL : w ∉ M.L.lattice := fun h => hw (hLL h)
  have hA : ∀ t ∈ T, ‖M.ι (M.L.weierstrassP w' - M.L.weierstrassP t)‖ = ‖M.ι (M.c ^ 2)‖ := by
    intro t ht
    have ht1 := (T1 t ht).1
    have hpt : ((2 * N : ℕ) : ℂ) * t ∈ M.L.lattice := by
      have h := add_mem (hN t ht1) (hN t ht1)
      convert h using 1; push_cast; ring
    refine dist_eq M hOk hc hp hpt hw'L (T1 t ht).2 ?_ ?_
    · intro h
      apply hw'
      have h' := sub_mem (hLL h) ht1
      convert h' using 1; ring
    · intro h
      apply hw'
      have h' := add_mem (hLL h) ht1
      convert h' using 1; ring
  have hB : ∀ t ∈ T, ‖M.ι (M.L.weierstrassP w' - M.L.weierstrassP (w + t))‖ =
      ‖M.ι (M.c ^ 2)‖ := by
    intro t ht
    have ht1 := (T1 t ht).1
    have hpt : ((2 * N : ℕ) : ℂ) * (w + t) ∈ M.L.lattice := by
      have h := add_mem (hN _ (hLL hw2)) (add_mem (hN t ht1) (hN t ht1))
      convert h using 1; push_cast; ring
    refine dist_eq M hOk hc hp hpt hw'L ?_ ?_ ?_
    · intro h
      apply hw
      have h' := sub_mem (hLL h) ht1
      convert h' using 1; ring
    · intro h
      apply hd
      have h' := sub_mem (sub_mem (hLL h) ht1) (hLL hw'2)
      convert h' using 1; ring
    · intro h
      apply hd
      have h' := sub_mem (neg_mem (hLL h)) ht1
      convert h' using 1; ring
  have hC : ‖M.ι (M.L.weierstrassP w' - M.L.weierstrassP w)‖ = ‖M.ι (M.c ^ 2)‖ := by
    refine dist_eq M hOk hc hp hpw hw'L hwL ?_ ?_
    · intro h
      apply hd
      have h' := sub_mem (hLL h) (hLL hw'2)
      convert h' using 1; ring
    · intro h
      apply hd
      have h' := neg_mem (hLL h)
      convert h' using 1; ring
  have hprod := GlobalTheory.T.weierstrassP_superlattice_half_period_prod M.L L' T w hLL T1 T2 T3 hw2 hw w' hw'
  have hn := congrArg (fun z => ‖M.ι z‖) hprod
  simp only [map_mul, map_prod, norm_mul, norm_prod] at hn
  rw [Finset.prod_congr rfl hA, Finset.prod_congr rfl hB, hC, Finset.prod_const] at hn
  exact ⟨mul_right_cancel₀ (pow_ne_zero _ hγ) hn, hC⟩

private lemma notMem_lattice_of_two_mul_mem_of_odd_index {L L' : PeriodPair} {N : ℕ} (hodd : Odd N)
    (hN : ∀ x ∈ L'.lattice, (N : ℂ) * x ∈ L.lattice) {u : ℂ} (h2 : 2 * u ∈ L.lattice)
    (hu : u ∉ L.lattice) : u ∉ L'.lattice := by
  intro h
  obtain ⟨k, rfl⟩ := hodd
  apply hu
  have h3 : (k : ℂ) * (2 * u) ∈ L.lattice := by
    have h4 := nsmul_mem h2 k
    rwa [nsmul_eq_mul] at h4
  have h5 := sub_mem (hN u h) h3
  convert h5 using 1; push_cast; ring

theorem norm_disc_eq : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (L' : PeriodPair) (N : ℕ), q ≠ 2 → M.Ok → Nat.Coprime N (2 * q) →
    M.L.lattice ≤ L'.lattice → (∀ x ∈ L'.lattice, (N : ℂ) * x ∈ M.L.lattice) →
    ‖M.ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖M.ι (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2)‖ := by
  intro q hq M L' N hq2 hOk hN hLL hNL
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hN
    omega
  have hodd : Odd N := by
    have h2 : Nat.Coprime N 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 q) hN
    rcases Nat.even_or_odd N with he | ho
    · exfalso
      have h3 : 2 ∣ Nat.gcd N 2 := Nat.dvd_gcd (even_iff_two_dvd.mp he) dvd_rfl
      rw [Nat.Coprime.gcd_eq_one h2] at h3
      omega
    · exact ho
  have hNq : Nat.Coprime N q := Nat.Coprime.coprime_dvd_right (dvd_mul_left q 2) hN
  have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq.out).mpr (Ne.symm hq2)
  have hc : Nat.Coprime (2 * N) q := Nat.Coprime.mul_left h2q hNq
  have hc0 : M.c ≠ 0 := by
    have h := hOk
    unfold GlobalTheory.MomOne.Mdl.Ok at h
    exact h.1
  have hγ : ‖M.ι (M.c ^ 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((map_ne_zero M.ι).mpr (pow_ne_zero 2 hc0))
  have nz : ∀ {x : ℂ}, ‖M.ι x‖ = ‖M.ι (M.c ^ 2)‖ → x ≠ 0 := by
    intro x hx h0
    apply hγ
    rw [← hx, h0, map_zero, norm_zero]
  obtain ⟨T, T1, T2, T3⟩ := exists_reps M.L L' N hN0 hLL hNL
  have hω₁ := M.L.ω₁_mem_lattice
  have hω₂ := M.L.ω₂_mem_lattice
  have a1 : 2 * (M.L.ω₁ / 2) ∈ M.L.lattice := by convert hω₁ using 1; ring
  have a2 : 2 * (M.L.ω₂ / 2) ∈ M.L.lattice := by convert hω₂ using 1; ring
  have a3 : 2 * ((M.L.ω₁ + M.L.ω₂) / 2) ∈ M.L.lattice := by
    convert add_mem hω₁ hω₂ using 1; ring
  have n1 : M.L.ω₁ / 2 ∉ M.L.lattice := M.L.ω₁_div_two_notMem_lattice
  have n2 : M.L.ω₂ / 2 ∉ M.L.lattice := M.L.ω₂_div_two_notMem_lattice
  have n3 : (M.L.ω₁ + M.L.ω₂) / 2 ∉ M.L.lattice := by
    intro h
    have h' := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := M.L) (α := 1 / 2)
      (β := 1 / 2)).not.mpr (by norm_num)
    apply h'
    convert h using 1; push_cast; ring
  have d21 : 2 * (M.L.ω₂ / 2 - M.L.ω₁ / 2) ∈ M.L.lattice := by
    convert sub_mem hω₂ hω₁ using 1; ring
  have e21 : M.L.ω₂ / 2 - M.L.ω₁ / 2 ∉ M.L.lattice := by
    intro h
    apply n3
    convert add_mem h hω₁ using 1; ring
  have d31 : 2 * ((M.L.ω₁ + M.L.ω₂) / 2 - M.L.ω₁ / 2) ∈ M.L.lattice := by
    convert hω₂ using 1; ring
  have e31 : (M.L.ω₁ + M.L.ω₂) / 2 - M.L.ω₁ / 2 ∉ M.L.lattice := by
    intro h
    apply n2
    convert h using 1; ring
  have d32 : 2 * ((M.L.ω₁ + M.L.ω₂) / 2 - M.L.ω₂ / 2) ∈ M.L.lattice := by
    convert hω₁ using 1; ring
  have e32 : (M.L.ω₁ + M.L.ω₂) / 2 - M.L.ω₂ / 2 ∉ M.L.lattice := by
    intro h
    apply n1
    convert h using 1; ring
  have m1 := notMem_lattice_of_two_mul_mem_of_odd_index hodd hNL a1 n1
  have m2 := notMem_lattice_of_two_mul_mem_of_odd_index hodd hNL a2 n2
  have m3 := notMem_lattice_of_two_mul_mem_of_odd_index hodd hNL a3 n3
  have k12 := key M L' N hOk hc hLL hNL T T1 T2 T3 a2 a1 m2 m1 (notMem_lattice_of_two_mul_mem_of_odd_index hodd hNL d21 e21)
  have k13 := key M L' N hOk hc hLL hNL T T1 T2 T3 a3 a1 m3 m1 (notMem_lattice_of_two_mul_mem_of_odd_index hodd hNL d31 e31)
  have k23 := key M L' N hOk hc hLL hNL T T1 T2 T3 a3 a2 m3 m2 (notMem_lattice_of_two_mul_mem_of_odd_index hodd hNL d32 e32)
  rw [disc_of_roots (cubic_root L' (hLL a1) m1) (cubic_root L' (hLL a2) m2)
      (cubic_root L' (hLL a3) m3) (nz k12.1) (nz k13.1) (nz k23.1),
    disc_of_roots (cubic_root M.L a1 n1) (cubic_root M.L a2 n2) (cubic_root M.L a3 n3)
      (nz k12.2) (nz k13.2) (nz k23.2)]
  simp only [map_mul, map_pow, norm_mul, norm_pow, k12.1, k13.1, k23.1, k12.2, k13.2, k23.2]

end GlobalTheory.MomDisc
