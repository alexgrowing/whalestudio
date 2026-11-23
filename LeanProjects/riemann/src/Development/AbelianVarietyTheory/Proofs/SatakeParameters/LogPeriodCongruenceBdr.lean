import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat

theorem exists_mul_eq_pow_pred {l : ℕ} [Fact l.Prime] {j m : ℕ} (hj : j ≠ 0) (hm : ¬ l ^ m ∣ j) :
    ∃ c : ℤ_[l], ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ (m - 1) := by
  first
  | exact @_root_.GlobalTheory.PolynomialNormBound.main
  | exact _root_.GlobalTheory.PolynomialNormBound.main
  | (apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialNormBound.main ..)

theorem not_pow_dvd {l m j : ℕ} (h1 : j ≠ 0) (h2 : j < 2 * l ^ m) (h3 : j ≠ l ^ m) : ¬ l ^ m ∣ j := by
  rintro ⟨t, rfl⟩
  rcases t with _ | _ | t
  · simp at h1
  · simp at h3
  · have : l ^ m * 2 ≤ l ^ m * (t + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem log_trunc_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : Per.BdRp l) * (((l : ℕ) : Per.BdRp l) ^ (m - 1) * u - s) -
      e * betaD ϖ ^ (l ^ m) := by
  intro l _ ϖ hker hfil u hu m hm
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set M := l ^ (m + 1) with hM
  set n := 2 * M with hn
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  have hMpos : 0 < M := pow_pos hlpos _
  set β := beta ϖ with hβ

  have hc : ∀ j : ℕ, ∃ c : ℤ_[l], (j ≠ 0 ∧ j < n ∧ j ≠ M) → ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ m := by
    intro j
    by_cases h : j ≠ 0 ∧ j < n ∧ j ≠ M
    · obtain ⟨c, hc⟩ := exists_mul_eq_pow_pred (l := l) (m := m + 1) h.1 (not_pow_dvd h.1 h.2.1 h.2.2)
      exact ⟨c, fun _ => by simpa using hc⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose c hc using hc
  let d : ℕ → ℤ_[l] := fun j => if j = M ∨ j = n then 0 else c j
  let a : ℕ → Per.AinfP l := fun k => (-1) ^ k * Per.zP l (d (k + 1)) * β ^ (k + 1)
  let S : Per.AinfP l := ∑ k ∈ Finset.range n, a k
  let e0 : Per.AinfP l := (-1) ^ (M - 1)
  let T : Per.AinfP l := (-1) ^ (n - 1) * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
    ((n.factorial / (n - 1 + 1) : ℕ) : Per.AinfP l) * β ^ (n - 1 + 1)
  have hS : S ∈ Sa ϖ := by
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ _) ?_) (Subalgebra.pow_mem _ ?_ _)
    · exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
    · first
      | exact Subalgebra.algebraMap_mem _ _
      | (rw [GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]; exact Subalgebra.algebraMap_mem _ _)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)

  have hterm : ∀ k ∈ Finset.range n, ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
      ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1)) =
      ((n.factorial : ℕ) : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) * a k +
      (if k = M - 1 then ((n.factorial : ℕ) : Per.AinfP l) * ((-1) ^ k * β ^ (k + 1)) else 0) +
      (if k = n - 1 then (-1) ^ k * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
        ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hdvd : (k + 1) ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
    have hq : (((n.factorial / (k + 1) : ℕ) : Per.AinfP l)) * ((k + 1 : ℕ) : Per.AinfP l) =
        ((n.factorial : ℕ) : Per.AinfP l) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    by_cases h1 : k = M - 1
    · have h2 : ¬ k = n - 1 := by omega
      have hk1 : k + 1 = M := by omega
      have hda : d (k + 1) = 0 := by simp [d, hk1]
      rw [if_pos h1, if_neg h2]
      simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
      rw [← hq, hk1, hM, Nat.cast_pow]
      ring
    · by_cases h2 : k = n - 1
      · have hk1 : k + 1 = n := by omega
        have hda : d (k + 1) = 0 := by simp [d, hk1]
        rw [if_neg h1, if_pos h2]
        simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
        ring
      · have hne : ¬ (k + 1 = M ∨ k + 1 = n) := by omega
        have hda : d (k + 1) = c (k + 1) := by simp only [d, hne, if_false]
        have hck := hc (k + 1) ⟨by omega, by omega, by omega⟩
        have hck' := congrArg (Per.zP l) hck
        rw [map_mul, map_natCast, map_pow, map_natCast] at hck'
        rw [if_neg h1, if_neg h2]
        simp only [a, hda, add_zero]
        rw [← hq]
        linear_combination -(-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) *
          ((l : ℕ) : Per.AinfP l) * hck'
  have hsum : ((l : ℕ) : Per.AinfP l) ^ (m + 1) * ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) =
      ((n.factorial : ℕ) : Per.AinfP l) * (((l : ℕ) : Per.AinfP l) * S + e0 * β ^ M) + T := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum]
    have hm1 : M - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hn1 : n - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    rw [if_pos hm1, if_pos hn1, Nat.sub_add_cancel (by omega : 1 ≤ M)]
    simp only [S, e0, T]
    ring
  have hβI : β ∈ Per.kerP l := by rw [hker]; exact Ideal.mem_span_singleton_self _
  have hT : T ∈ Per.kerP l ^ n := by
    have : β ^ (n - 1 + 1) ∈ Per.kerP l ^ n := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Ideal.pow_mem_pow hβI n
    exact Ideal.mul_mem_left _ _ this

  let s : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) S
  refine ⟨s, Subring.mem_map.2 ⟨S, hS, rfl⟩, algebraMap (Per.AinfP l) (Per.BdRp l) e0, ?_, ?_⟩
  · rcases neg_one_pow_eq_or (Per.AinfP l) (M - 1) with h | h
    · left; simp [e0, h]
    · right; simp [e0, h]
  · rw [← Ideal.mem_span_singleton, ← hfil]
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have hev : ∀ x : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
        Ideal.Quotient.mk _ x := fun x => GlobalTheory.RingIface.ev_alg l n x
    let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
    have hunit : IsUnit ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
      have := (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).map q
      rwa [map_natCast] at this
    have hqT : q T = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hT
    have hs2 := congrArg q hsum
    simp only [map_add, map_mul, map_pow, map_natCast, hqT, add_zero] at hs2
    have hun := hu n
    apply hunit.mul_left_cancel
    rw [mul_zero]
    simp only [betaD, map_sub, map_mul, map_pow, map_natCast, s, hev]
    change ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * (((l : ℕ) : _) * (((l : ℕ) : _) ^ m * Per.ev l n u - q S) -
      q e0 * q β ^ M) = 0
    change _ = q _ at hun
    linear_combination ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) ^ (m + 1) * hun + hs2

end GlobalTheory.Pst.StLat
