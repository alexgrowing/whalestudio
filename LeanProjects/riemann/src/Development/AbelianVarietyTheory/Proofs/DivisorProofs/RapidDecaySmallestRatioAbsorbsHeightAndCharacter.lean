import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOneStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.RapidDecayReal

theorem height_le (a : ℕ) (N : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (K : ℝ)
    (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ (1 + 2 * a * K) ^ N := by
  have h0 : 0 ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hr i).le)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (inv_pos.2 (hr i)).le)
    linarith
  apply pow_le_pow_left₀ h0
  have h1 : ∑ i, r i ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).1)
  have h2 : ∑ i, (r i)⁻¹ ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  linarith

theorem char_ge (a : ℕ) (lam : Fin a → ℝ) (L : ℕ) (hL : ∑ i, |lam i| ≤ L) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) (K : ℝ) (hK : 1 ≤ K) (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (K ^ L)⁻¹ ≤ ∏ i, r i ^ lam i := by
  have hK0 : 0 < K := by linarith
  have hi : ∀ i, K ^ (-|lam i|) ≤ r i ^ lam i := by
    intro i
    rcases le_or_gt 0 (lam i) with h | h
    · rw [abs_of_nonneg h, Real.rpow_neg hK0.le, ← Real.inv_rpow hK0.le]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ h
      rw [inv_le_comm₀ hK0 (hr i)]; exact (hb i).2
    · rw [abs_of_neg h, neg_neg]
      have e1 : K ^ lam i = (K⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
      have e2 : r i ^ lam i = ((r i)⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow (hr i).le, Real.rpow_neg (hr i).le, inv_inv]
      rw [e1, e2]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ (by linarith)
      exact inv_anti₀ (hr i) (hb i).1
  calc (K ^ L)⁻¹ = K ^ (-(L : ℝ)) := by rw [Real.rpow_neg hK0.le, Real.rpow_natCast]
    _ ≤ K ^ (∑ i, -|lam i|) := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        rw [Finset.sum_neg_distrib]; linarith
    _ = ∏ i, K ^ (-|lam i|) := Real.rpow_sum_of_pos hK0 _ _
    _ ≤ ∏ i, r i ^ lam i :=
        Finset.prod_le_prod (fun i _ => Real.rpow_nonneg hK0.le _) (fun i _ => hi i)

theorem key (a : ℕ) (lam : Fin a → ℝ) (L N : ℕ) (hL : ∑ i, |lam i| ≤ L) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hb : ∀ i, r i ≤ C0 * ρ ^ a ∧ (r i)⁻¹ ≤ C0 * ρ ^ a) :
    (ρ ^ (a * N + a * L))⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤
      ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i := by
  set P := ρ ^ a with hPdef
  have hP : 1 ≤ P := one_le_pow₀ hρ
  have hC00 : 0 < C0 := by linarith
  have hP0 : 0 < P := by linarith
  have hK : 1 ≤ C0 * P := by nlinarith
  have h1 := height_le a N r hr (C0 * P) hb
  have h2 := char_ge a lam L hL r hr (C0 * P) hK hb
  have h3 : (1 + 2 * (a : ℝ) * (C0 * P)) ^ N ≤ ((1 + 2 * a * C0) * P) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hm : ρ ^ (a * N + a * L) = P ^ N * P ^ L := by
    rw [hPdef, ← pow_mul, ← pow_mul, ← pow_add]
  rw [hm]
  calc (P ^ N * P ^ L)⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N
      ≤ (P ^ N * P ^ L)⁻¹ * ((1 + 2 * a * C0) * P) ^ N :=
        mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
    _ = ((1 + 2 * a * C0) ^ N * C0 ^ L) * ((C0 * P) ^ L)⁻¹ := by
        rw [mul_pow, mul_pow]
        field_simp
    _ ≤ ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end GlobalTheory.RapidDecayReal

open GlobalTheory.RapidDecayReal in

theorem GlobalTheory.rapidDecay_real : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  intro a t ht lam N
  obtain ⟨C0, hC0, hC⟩ := GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one a t ht
  set L := ⌈∑ i, |lam i|⌉₊ with hLdef
  have hL : ∑ i, |lam i| ≤ L := Nat.le_ceil _
  refine ⟨a * N + a * L, (1 + 2 * a * C0) ^ N * C0 ^ L, by positivity, ?_⟩
  intro r hr hcone hprod
  by_cases hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ r j
  · left
    have hb := hC r 1 hr hcone hprod le_rfl (fun i j hij => by rw [one_mul]; exact hall i j hij)
    have := key a lam L N hL C0 hC0 r hr 1 le_rfl hb
    simpa using this
  · right
    push_neg at hall
    obtain ⟨i, j, hij, hlt⟩ := hall
    set S := (Finset.univ : Finset (Fin a × Fin a)).filter (fun p => (p.2 : ℕ) = p.1 + 1) with hS
    have hne : S.Nonempty := ⟨(i, j), by simp [hS, hij]⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun p => r p.1 / r p.2) hne
    have hpadj : (p.2 : ℕ) = p.1 + 1 := by simpa [hS] using hp
    have hij' : r i / r j ≤ r p.1 / r p.2 := hmax (i, j) (by simp [hS, hij])
    have hρ : 1 ≤ r p.1 / r p.2 := by
      have : 1 < r i / r j := by rw [one_lt_div (hr j)]; exact hlt
      linarith
    have hadj : ∀ i' j' : Fin a, (j' : ℕ) = i' + 1 → r i' ≤ (r p.1 / r p.2) * r j' := by
      intro i' j' h'
      have := hmax (i', j') (by simp [hS, h'])
      rwa [div_le_iff₀ (hr j')] at this
    have hb := hC r _ hr hcone hprod hρ hadj
    refine ⟨p.1, p.2, hpadj, ?_⟩
    have := key a lam L N hL C0 hC0 r hr _ hρ hb
    rw [← inv_div (r p.1) (r p.2), inv_pow]
    exact this
