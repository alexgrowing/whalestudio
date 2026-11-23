import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicLogLe

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLossPrimes

theorem bound_one {D : D7} {L : SizeData₂ D} {c : ErrC}
    (hc : c.dig = 3) (P : ParameterChoice' D L) (hS : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| ≤ 2 * (9 * (1 / L.sc.eps + 1)) * L.B0 := by
  have hEg : ∀ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| = 2 * (Real.log (p : ℝ) * |(padicValNat p 1 : ℝ) +
    (if (p : ℝ) ≤ L.sc.X'' D.R.n then 3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a +
      (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1) else 0)|) := by
    intro p hp
    have e0 : padicValNat p 1 = 0 := by simp
    rw [if_pos (hQ p hp).2, e0, Nat.cast_zero, zero_add]
    unfold EatC Formalism.MainNotions.G.Nm
    rw [hc, mul_assoc]
  rw [Finset.sum_congr rfl hEg]
  rw [← Finset.mul_sum, mul_assoc (2 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hL := HCEntries.one_le_scL L
  have hb := HCEntries.one_le_b L
  have hk := HCEntries.one_le_k D
  have ht := HCEntries.one_le_letterBlockLength D
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hx0 : 0 < L.sc.x := by linarith
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha1 : 1 ≤ L.sc.a := by rw [ha]; exact one_le_mul_of_one_le_of_one_le (by linarith) hb
  have hN2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := one_le_pow₀ hN
  have hw : (D.R.N D.R.m : ℝ) ^ 2 * L.sc.x ≤ L.sc.w'' D.R.n := by
    have a1 := P.teta
    rw [le_div_iff₀ hx0] at a1
    exact (mul_le_mul_of_nonneg_right (hNη.trans (le_mul_of_one_le_left hη0 ht)) hx0.le).trans a1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := (one_le_mul_of_one_le_of_one_le hN2 (by linarith)).trans hw
  have hX0 : 0 ≤ L.sc.X'' D.R.n := by unfold Scale.X''; positivity
  have hXa : L.sc.X'' D.R.n ≤ L.sc.a := div_le_self (by linarith) hw1
  have hXN : L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2 ≤ L.sc.b := by
    unfold Scale.X''
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), ha]
    have := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ L.sc.b)
    linarith
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  have hwj := HCEntries.wj_bounds hS hx j hj1 hjm
  have hW0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ := Finset.sum_nonneg fun τ _ => (hwj τ).1
  have hcard : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  have hW : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => wj D j τ) _ fun τ _ => (hwj τ).2
    rwa [Finset.card_univ, hcard, nsmul_eq_mul] at this
  have hla0 : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have he := L.sc.eps_pos
  have hla : Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.sc.L := by
    rw [ha, Real.log_mul hx0.ne' (by linarith)]
    have a1 : Real.log L.sc.b = L.sc.L := Real.log_exp _
    have a2 : Real.log L.sc.x ≤ L.sc.L / L.sc.eps := Real.log_le_rpow_div hx0.le he
    rw [a1]
    calc _ ≤ L.sc.L / L.sc.eps + L.sc.L := by linarith
      _ = _ := by ring
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hfb : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    have : L.B0 = D.R.m * (D.R.f * L.sc.b * L.sc.L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) hm
  have hfl : D.R.f * L.sc.b * Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.B0 := by
    calc _ ≤ D.R.f * L.sc.b * ((1 / L.sc.eps + 1) * L.sc.L) := mul_le_mul_of_nonneg_left hla hfb
      _ = (1 / L.sc.eps + 1) * (D.R.f * L.sc.b * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : L.sc.X'' D.R.n * (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.log L.sc.a) ≤
      3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ = 3 * (D.R.f * (L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2) * Real.log L.sc.a) := by ring
      _ ≤ _ := by gcongr
  have t3 : (∑ τ : D.what₂.Tau, wj D j τ) * Real.log L.sc.a ≤ 3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ ≤ D.R.f * (3 * L.sc.b) * Real.log L.sc.a := mul_le_mul_of_nonneg_right hW hla0
      _ = _ := by ring
  have key := GlobalTheory.ConjLoss.sum_primes_le Q (fun p hp => (hQ p hp).1)
    1 (L.sc.X'' D.R.n) L.sc.a (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2)
    (∑ τ : D.what₂.Tau, wj D j τ) hX0 hXa ha1 (by positivity) hW0
  refine key.trans ?_
  rw [Nat.cast_one, Real.log_one]
  linarith

theorem loss_sum_primes : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm h0 h1
  refine ⟨2 * (9 * (1 / eps + 1)), 2, by positivity, ?_⟩
  intro x hx0 hx i j hj Q hQ
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have := bound_one (c := Fm.cX.err) Fm.fixed.2.2.2.2.2.1 (Fm.params x hx i) (Fm.sizes x hx i)
    (by rw [hsx]; exact hx0) j hj Q hQ
  rwa [hse] at this

end GlobalTheory.ConjLossPrimes

end
