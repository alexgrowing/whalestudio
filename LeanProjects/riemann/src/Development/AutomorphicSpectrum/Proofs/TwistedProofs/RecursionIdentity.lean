import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertLevi

def aTerm (q N : ℕ) (X α : ℂ) (a : ℤ) : ℂ :=
  (q : ℂ) ^ ((2 * N + 2) * a.toNat) * X ^ a.natAbs * (α ^ a * (q : ℂ) ^ (-a * ((N : ℤ) + 1)))

theorem aTerm_nat {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (k : ℕ) :
    aTerm q N X α (k : ℤ) = ((q : ℂ) ^ (N + 1) * X * α) ^ k := by
  have h : (q : ℂ) ^ (-(k : ℤ) * ((N : ℤ) + 1)) = ((q : ℂ) ^ ((N + 1) * k))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast
    ring
  have h2 : (q : ℂ) ^ ((2 * N + 2) * k) = (q : ℂ) ^ ((N + 1) * k) * (q : ℂ) ^ ((N + 1) * k) := by
    rw [← pow_add]
    congr 1
    ring
  have h3 : (q : ℂ) ^ ((N + 1) * k) ≠ 0 := pow_ne_zero _ hq
  rw [aTerm, h, Int.toNat_natCast, Int.natAbs_natCast, zpow_natCast, h2, mul_pow, mul_pow, ← pow_mul]
  field_simp

theorem aTerm_neg {q N : ℕ} {X α : ℂ} (k : ℕ) :
    aTerm q N X α (-((k : ℤ) + 1)) = ((q : ℂ) ^ (N + 1) * X / α) * ((q : ℂ) ^ (N + 1) * X / α) ^ k := by
  have h : (q : ℂ) ^ (-(-((k : ℤ) + 1)) * ((N : ℤ) + 1)) = (q : ℂ) ^ ((N + 1) * (k + 1)) := by
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  have h1 : (-((k : ℤ) + 1)).toNat = 0 := by omega
  have h2 : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
  have h3 : α ^ (-((k : ℤ) + 1)) = (α ^ (k + 1))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [aTerm, h, h1, h2, h3, ← pow_succ', div_pow, mul_pow, ← pow_mul]
  simp only [mul_zero, pow_zero, one_mul, div_eq_mul_inv]
  ring

theorem hasSum_aTerm {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (h1 : ‖(q : ℂ) ^ (N + 1) * X * α‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X / α‖ < 1) :
    HasSum (aTerm q N X α) ((1 - (q : ℂ) ^ (N + 1) * X * α)⁻¹ +
      ((q : ℂ) ^ (N + 1) * X / α) * (1 - (q : ℂ) ^ (N + 1) * X / α)⁻¹) := by
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · simp only [aTerm_nat hq]
    exact hasSum_geometric_of_norm_lt_one h1
  · simp only [aTerm_neg]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left _

theorem step : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hya hyb H hZ
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy' : ‖(q : ℂ) ^ (N + 1) * X‖ < 1 := hy ▸ hy1
  have h1 : ‖y * α‖ < 1 := by rwa [norm_mul]
  have h2 : ‖y / α‖ < 1 := by rwa [norm_div, div_eq_mul_inv]
  have hA := hasSum_aTerm (N := N) (X := X) (α := α) hq0 (hy ▸ h1) (hy ▸ h2)
  rw [← hy] at hA
  set A := aTerm q N X α with hAdef
  set B : Y → ℂ := fun b => ((q : ℂ) ^ 2 * X) ^ l b * φ₀ b with hBdef
  set w : ℤ × Y → ℂ := fun p => α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * φ₀ p.2 with hw
  set f : (ℤ × Y) × C → ℂ := fun p => X ^ ℓ p.1.1 p.1.2 p.2 *
    (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2) with hf
  have hAn : Summable fun a => ‖A a‖ := hA.summable.norm
  have hBn : Summable fun b => ‖B b‖ := hZ.summable.norm
  have hABn : Summable fun p : ℤ × Y => ‖A p.1‖ * ‖B p.2‖ :=
    hAn.mul_of_nonneg hBn (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hAB : Summable fun p : ℤ × Y => A p.1 * B p.2 :=
    Summable.of_norm (by simpa only [norm_mul] using hABn)
  have key : ∀ (X' : ℂ) (p : ℤ × Y), (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X' ^ (p.1.natAbs + l p.2) *
      (α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * φ₀ p.2) =
      aTerm q N X' α p.1 * (((q : ℂ) ^ 2 * X') ^ l p.2 * φ₀ p.2) := by
    intro X' p
    rw [aTerm]
    generalize α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) = t
    ring

  have hin : ∀ p : ℤ × Y, HasSum (fun c => f (p, c)) (jFac q N X * (A p.1 * B p.2)) := by
    intro p
    have := (H X hy' p.1 p.2).mul_right (w p)
    have e : (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2) * w p = A p.1 * B p.2 := key X p
    have e' : jFac q N X * (A p.1 * B p.2) = (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) *
        X ^ (p.1.natAbs + l p.2) * jFac q N X * w p := by
      rw [← e]
      ring
    rw [e']
    exact this

  have hX' : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, norm_norm] using hy'
  have hR : ∀ p : ℤ × Y, ∃ v : ℝ, HasSum (fun c => ‖f (p, c)‖) v ∧
      v ≤ ‖jFac q N (‖X‖ : ℝ)‖ * (‖A p.1‖ * ‖B p.2‖) := by
    intro p
    have h3 := Complex.hasSum_re (H _ hX' p.1 p.2)
    have h4 := h3.mul_right ‖w p‖
    refine ⟨((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (p.1.natAbs + l p.2) *
      jFac q N (‖X‖ : ℝ)).re * ‖w p‖, ?_, ?_⟩
    · have e : (fun c => ‖f (p, c)‖) = fun c => (((‖X‖ : ℝ) : ℂ) ^ ℓ p.1 p.2 c).re * ‖w p‖ := funext fun c => by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
        change ‖X ^ ℓ p.1 p.2 c * w p‖ = _
        rw [norm_mul, norm_pow]
      rw [e]
      exact h4
    · have e : ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2)‖ * ‖w p‖ =
          ‖A p.1‖ * ‖B p.2‖ := by
        rw [← norm_mul, ← norm_mul]
        exact congrArg norm (key X p)
      have e2 : ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (p.1.natAbs + l p.2) *
          jFac q N (‖X‖ : ℝ)‖ = ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2)‖ *
          ‖jFac q N (‖X‖ : ℝ)‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_real, norm_norm]
      refine (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)).trans (le_of_eq ?_)
      rw [e2, ← e]
      ring
  choose v hv1 hv2 using hR
  have hfs : Summable f := by
    refine Summable.of_norm ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun p => (hv1 p).summable, ?_⟩)
    have e : (fun p => ∑' c, ‖f (p, c)‖) = v := funext fun p => (hv1 p).tsum_eq
    rw [e]
    exact Summable.of_nonneg_of_le (fun p => (hv1 p).nonneg fun _ => norm_nonneg _) hv2 (hABn.mul_left _)
  have h5 := hfs.hasSum.prod_fiberwise hin
  have h6 := (hA.mul hZ hAB).mul_left (jFac q N X)
  have h7 := h5.unique h6
  have hy2 : 1 - y ^ 2 ≠ 0 := fun h => by
    have e : y ^ 2 = 1 := by linear_combination -h
    have e2 : ‖y‖ ^ 2 = 1 := by rw [← norm_pow, e, norm_one]
    have : ‖y‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hy1 two_ne_zero
    linarith
  have hd1 : 1 - y * α ≠ 0 := fun h => by
    have e : y * α = 1 := by linear_combination -h
    rw [e, norm_one] at h1
    exact lt_irrefl _ h1
  have hd2 : 1 - y / α ≠ 0 := fun h => by
    have e : y / α = 1 := by linear_combination -h
    rw [e, norm_one] at h2
    exact lt_irrefl _ h2
  have hval : (1 - X) * (1 + q * X) * ((1 - y * α)⁻¹ * (1 - y / α)⁻¹) * Z =
      jFac q N X * (((1 - y * α)⁻¹ + y / α * (1 - y / α)⁻¹) * Z) := by
    obtain ⟨t, ht⟩ : ∃ t, t = y / α := ⟨_, rfl⟩
    have htα : t * α = y := by rw [ht]; field_simp
    rw [← ht] at hd2 ⊢
    have e : (1 - y * α)⁻¹ + t * (1 - t)⁻¹ = (1 - y ^ 2) * ((1 - y * α)⁻¹ * (1 - t)⁻¹) := by
      field_simp
      linear_combination (-y) * htα
    rw [e, jFac, ← hy]
    field_simp
  rw [hval, ← h7]
  exact hfs.hasSum

end GlobalTheory.CompanionTheory.InertLevi

end
