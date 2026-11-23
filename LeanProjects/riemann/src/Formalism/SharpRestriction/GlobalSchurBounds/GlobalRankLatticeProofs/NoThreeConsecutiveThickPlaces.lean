import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

def InertPart (D : D7) : Prop :=
  ∀ φ₀ : G0, (φ₀ = c0 ∨ φ₀ = sgc0) → ∀ h : HH D,
    (∀ p : ℕ, p.Prime → (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) = 1 →
      frob D p = gOf D φ₀ h →
      ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (span {(p : ℤ)}) →
        (Inert D 𝔭 ↔ φ₀ = c0 ∧ Odd (addOrderOf h)))

theorem tau_one_mem_orbit_set (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := by
  show φ.chD (φ.tau1 t) = 1
  rfl

private theorem neg_one_of_ne {x : ℤˣ} (h : x ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · exact absurd hx h
  · exact hx

private theorem no_three (R : Formalism.HC.Frame) {L : ℕ} (T : Finset ℕ) (hTr : ∀ s ∈ T, 4 * L * s < R.n0)
    (hTn : NoRel T L) (u0 : R.A) (hL : 3 ≤ L) (φ : R.GG) (hφ : φ ∉ R.Psi) (hφc : φ ≠ R.cc)
    (τ : R.GG) (hτ : τ ∈ R.Psi) (i : ℕ)
    (h0 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ i * τ) = R.tau2 (R.dig s + u0))
    (h1 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 1) * τ) = R.tau2 (R.dig s + u0))
    (h2 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 2) * τ) = R.tau2 (R.dig s + u0)) : False := by
  have key : ∀ (y : R.GG), (Formalism.HC.Frame.placeOf y).1.1 = -1 →
      (Formalism.HC.Frame.placeOf (φ * y)).1.1 = -1 → φ.1.1 = -1 := by
    intro y h0 h1
    have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
    simp only [Formalism.HC.Frame.placeOf] at h0 h1
    rcases Int.units_eq_one_or y.1.2 with hy | hy
    · rw [if_pos hy] at h0
      have hm : (φ * y).1.2 = -1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_neg (by rw [hm]; decide)] at h1
      simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul, h0] using h1
    · rw [if_neg (by rw [hy]; decide)] at h0
      have hm : (φ * y).1.2 = 1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_pos hm] at h1
      have h0' : y.1.1 = 1 := by
        simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul] using h0
      simpa [Prod.fst_mul, h0'] using h1
  have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
  obtain ⟨s1, hs1, e1⟩ := h0
  obtain ⟨s2, hs2, e2⟩ := h1
  obtain ⟨s3, hs3, e3⟩ := h2
  have hφ1 : φ.1.1 = -1 := key (φ ^ i * τ) (by rw [e1]; rfl)
    (by rw [← mul_assoc, ← pow_succ', e2]; rfl)
  have E : ∀ (k s : ℕ), Formalism.HC.Frame.placeOf (φ ^ k * τ) = R.tau2 (R.dig s + u0) →
      k • R.iotaInv φ.2 + R.iotaInv τ.2 = R.dig s + u0 := by
    intro k s hk
    have this : R.iotaInv (Formalism.HC.Frame.placeOf (φ ^ k * τ)).2 = R.iotaInv (R.tau2 (R.dig s + u0)).2 := by
      rw [hk]
    rw [Formalism.HC.Frame.placeOf_snd, Prod.snd_mul, Prod.pow_snd, Formalism.HC.Frame.iotaInv_mul,
      Formalism.HC.Frame.iotaInv_pow] at this
    change _ = R.iotaInv (R.iota _) at this
    rw [Formalism.HC.Frame.iotaInv_iota] at this
    exact this
  have E1 := E i s1 e1
  have E2 := E (i + 1) s2 e2
  have E3 := E (i + 2) s3 e3
  set x := R.iotaInv φ.2 with hxdef
  set T0 := R.iotaInv τ.2
  have hx1 : R.dig s2 - R.dig s1 = x := by
    have a : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    have b : R.dig s1 = (i • x + T0) - u0 := by rw [E1]; abel
    rw [a, b, succ_nsmul]
    abel
  have hx2 : R.dig s3 - R.dig s2 = x := by
    have a : R.dig s3 = ((i + 2) • x + T0) - u0 := by rw [E3]; abel
    have b : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    rw [a, b, show i + 2 = (i + 1) + 1 from rfl, succ_nsmul]
    abel
  have hx0 : x ≠ 0 := by
    intro h0
    apply hφc
    have h2 : φ.2 = 1 := (R.iotaInv_eq_zero_iff _).1 h0
    exact Prod.ext (Prod.ext hφ1 hφ2) h2
  have hzero : ((s1 : ℤ) + s3 - s2 - s2) • R.a0 = 0 := by
    rw [sub_zsmul, sub_zsmul, add_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]
    change R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 = 0
    have : R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 =
        (R.dig s3 - R.dig s2) - (R.dig s2 - R.dig s1) := by abel
    rw [this, hx1, hx2, sub_self]
  have hdvd : (R.n0 : ℤ) ∣ (s1 : ℤ) + s3 - s2 - s2 := addOrderOf_dvd_iff_zsmul_eq_zero.2 hzero
  have b1 := hTr s1 hs1
  have b2 := hTr s2 hs2
  have b3 := hTr s3 hs3
  have c1 : 12 * s1 ≤ 4 * L * s1 := Nat.mul_le_mul_right s1 (by omega)
  have c2 : 12 * s2 ≤ 4 * L * s2 := Nat.mul_le_mul_right s2 (by omega)
  have c3 : 12 * s3 ≤ 4 * L * s3 := Nat.mul_le_mul_right s3 (by omega)
  have habs : |(s1 : ℤ) + s3 - s2 - s2| < R.n0 := abs_lt.2 ⟨by omega, by omega⟩
  have hrel : (s1 : ℤ) + s3 - s2 - s2 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have n12 : s1 ≠ s2 := by
    rintro rfl
    exact hx0 (by rw [← hx1, sub_self])
  have n23 : s2 ≠ s3 := by
    rintro rfl
    exact hx0 (by rw [← hx2, sub_self])
  have n13 : s1 ≠ s3 := by
    rintro rfl
    apply n12
    omega
  apply hTn s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 1 2 (by norm_num) (by norm_num; omega) (by norm_num)
    (by norm_num; omega) (by norm_num)
  linarith

theorem even_addOrderOf_of_h_ne_zero (D : D7) {h : D.R.A} (hh : D.R.h h ≠ 0) : Even (addOrderOf h) := by
  have h1 : addOrderOf (D.R.h h) ∣ addOrderOf h := addOrderOf_map_dvd D.R.h h
  have h2 : addOrderOf (D.R.h h) ∣ 2 ^ D.R.e := by
    have := D.R.orderOf_H_dvd (Additive.toMul (D.R.h h))
    rwa [← addOrderOf_ofMul_eq_orderOf, ofMul_toMul] at this
  have h3 : addOrderOf (D.R.h h) ≠ 1 := by
    intro hx
    apply hh
    have := addOrderOf_nsmul_eq_zero (D.R.h h)
    rwa [hx, one_nsmul] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h3 (by simpa using hk')
  rw [even_iff_two_dvd]
  refine dvd_trans ?_ h1
  rw [hk']
  exact dvd_pow_self 2 hk0

theorem cc_mem_zpowers_gOf (D : D7) (φ₀ : G0) (h : HH D) :
    D.R.cc ∈ Subgroup.zpowers (gOf D φ₀ h) ↔ φ₀ = c0 ∧ Odd (addOrderOf h) := by
  have hu : ∀ (u : ℤˣ) (k : ℤ), u ^ k = -1 → u = -1 ∧ Odd k := by
    intro u k huk
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [one_zpow] at huk
      exact absurd huk (by decide)
    · refine ⟨rfl, ?_⟩
      rcases Int.even_or_odd k with he | ho
      · rw [he.neg_one_zpow] at huk
        exact absurd huk (by decide)
      · exact ho
  have hc0sq : c0 ^ 2 = 1 := by
    ext <;> simp [c0]
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    have e1 : φ₀ ^ k = c0 := congrArg Prod.fst hk
    have e2 : (Multiplicative.ofAdd h) ^ k = 1 := congrArg Prod.snd hk
    have e2' : k • h = 0 := by
      have := congrArg Multiplicative.toAdd e2
      simpa using this
    have a1 := hu _ _ (congrArg Prod.fst e1)
    have a2 := hu _ _ (congrArg Prod.snd e1)
    refine ⟨Prod.ext a1.1 a2.1, ?_⟩
    have hd : (addOrderOf h : ℤ) ∣ k := addOrderOf_dvd_iff_zsmul_eq_zero.2 e2'
    have hd' : addOrderOf h ∣ k.natAbs := Int.natCast_dvd.1 hd
    exact Odd.of_dvd_nat (Int.natAbs_odd.2 a1.2) hd'
  · rintro ⟨rfl, hodd⟩
    refine ⟨(addOrderOf h : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · change c0 ^ ((addOrderOf h : ℕ) : ℤ) = c0
      rw [zpow_natCast]
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hc0sq, one_pow, one_mul]
    · change (Multiplicative.ofAdd h) ^ ((addOrderOf h : ℕ) : ℤ) = 1
      rw [zpow_natCast, ← ofAdd_nsmul, addOrderOf_nsmul_eq_zero, ofAdd_zero]

theorem lemma_one_three_of_inert (D : D7) (hI : InertPart D) : PointsLemma D := by
  intro φ₀ hφ₀ h
  have hg1 : (gOf D φ₀ h).1 = φ₀ := rfl
  have hsg : sgc0 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    ext <;> simp [sgc0, c0]
  have hg : (gOf D φ₀ h).1 = c0 ∨ (gOf D φ₀ h).1 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    rw [hg1, ← hsg]
    exact hφ₀
  have hchg : D.R.chD (gOf D φ₀ h) = -1 := by
    change φ₀.2 = -1
    rcases hφ₀ with rfl | rfl
    · rfl
    · rw [hsg]
  have hcc : D.R.chD D.R.cc = -1 := rfl
  refine ⟨?_, ?_, ?_, ?_, cc_mem_zpowers_gOf D φ₀ h, hI φ₀ hφ₀ h, ?_⟩
  · intro τ hτ i
    have hτ' : D.R.chD τ = 1 := hτ
    constructor
    · intro he
      show D.R.chD _ = 1
      rw [map_mul, map_pow, hchg, hτ', he.neg_one_pow, one_mul]
    · intro ho
      refine ⟨D.R.cc * ((gOf D φ₀ h) ^ i * τ), ?_, ?_⟩
      · show D.R.chD _ = 1
        rw [map_mul, map_mul, map_pow, hchg, hτ', ho.neg_one_pow, hcc]
        decide
      · rw [← mul_assoc, cc_mul_cc, one_mul]
  · intro t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).1
    show D.R.iotaInv (Formalism.HC.Frame.placeOf _).2 = _
    rw [this, Formalism.HC.Frame.iotaInv_mul, Formalism.HC.Frame.iotaInv_pow]
    change i • D.R.iotaInv (D.R.iota h) + D.R.iotaInv (D.R.iota t) = t + i • h
    rw [Formalism.HC.Frame.iotaInv_iota, Formalism.HC.Frame.iotaInv_iota, add_comm]
  · intro hc t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.1
      (by rw [hg1]; exact hc)
    rw [this]
    rfl
  · intro hs t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.2
      (by rw [hg1, hs, hsg])
    rw [this]
    exact mul_one _
  · intro hc τ hτ
    refine ⟨?_, even_addOrderOf_of_h_ne_zero D⟩
    rw [Formalism.HC.Frame.hostOrbitCount (φ := D.R.toFrame) _ (by rw [hg1]; exact hc) τ hτ]
    exact orderOf_ofAdd_eq_addOrderOf h

theorem no_three_consecutive_thick_places (D : D7) : TorusPairsWithVariant D := by
  intro hL φ hφ hφc τ hτ i ⟨h0, h1, h2⟩
  have mem : ∀ g : D.R.GG, g ∈ thick D → ∃ s ∈ D.host.T2, g = D.R.tau2 (D.R.dig s + D.host.u0) := by
    intro g hg
    obtain ⟨s, hs, he⟩ := Finset.mem_image.1 hg
    exact ⟨s, hs, he.symm⟩
  exact no_three D.R.toFrame D.host.T2 D.host.second_set_range D.host.second_set_no_relation D.host.u0 hL φ hφ hφc τ hτ i
    (mem _ h0) (mem _ h1) (mem _ h2)

end Formalism.MainNotions.UnusedSlot33

end
