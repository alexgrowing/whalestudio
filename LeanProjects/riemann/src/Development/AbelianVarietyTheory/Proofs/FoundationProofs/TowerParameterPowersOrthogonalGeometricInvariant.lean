import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricFixedMemClosureFiniteAlgZpStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterNotPowModMaximalIdealAdjoinAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueTowerPowersLinearIndependentStatement
open GlobalTheory.K5

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem p_ne_zero' (h : IsClo p Ω) : (p : Ω) ≠ 0 := by
  haveI := GlobalTheory.K5.Basic.charZero_of_isClo h
  exact_mod_cast hp.out.ne_zero

theorem not_isInt_inv_p (h : IsClo p Ω) : ¬ IsInt p ((p : Ω)⁻¹) := by
  intro hi
  apply GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
  refine ⟨(p : Ω)⁻¹, hi, ?_⟩
  rw [pow_one, sub_zero, mul_inv_cancel₀ (p_ne_zero' h)]

theorem isInt_natPow_p (k : ℕ) : IsInt p ((p : Ω) ^ k) := by
  have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  simpa using this

theorem isInt_div (h : IsClo p Ω) {x y : Ω} (hy : y ≠ 0) {a a' : ℤ} {b b' : ℕ} (hb : 0 < b)
    (hb' : 0 < b') (h1 : IsInt p (x ^ b / (p : Ω) ^ a)) (h2 : IsInt p ((p : Ω) ^ a' / y ^ b'))
    (hle : (a' : ℚ) / b' ≤ a / b) : IsInt p (x / y) := by
  have hp0 := p_ne_zero' h
  have he : 0 ≤ a * b' - a' * b := by
    have hb0 : (0 : ℚ) < b := by exact_mod_cast hb
    have hb0' : (0 : ℚ) < b' := by exact_mod_cast hb'
    rw [div_le_div_iff₀ hb0' hb0] at hle
    have : (a' * b : ℚ) ≤ a * b' := hle
    exact_mod_cast (sub_nonneg.2 this)
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le he
  have key : (x / y) ^ (b * b') = (x ^ b / (p : Ω) ^ a) ^ b' * ((p : Ω) ^ a' / y ^ b') ^ b *
      (p : Ω) ^ e := by
    have hpe : (p : Ω) ^ e = ((p : Ω) ^ a) ^ b' / ((p : Ω) ^ a') ^ b := by
      rw [← zpow_natCast, ← he', zpow_sub₀ hp0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [hpe]
    have hP : (p : Ω) ^ a ≠ 0 := zpow_ne_zero _ hp0
    have hP' : (p : Ω) ^ a' ≠ 0 := zpow_ne_zero _ hp0
    generalize (p : Ω) ^ a = P at *
    generalize (p : Ω) ^ a' = P' at *
    have e1 : (y ^ b') ^ b = y ^ (b * b') := by rw [← pow_mul, mul_comm]
    have e2 : (x ^ b) ^ b' = x ^ (b * b') := by rw [← pow_mul]
    simp only [div_pow, e1, e2]
    have h3 : (P ^ b') ≠ 0 := pow_ne_zero _ hP
    have h4 : (P' ^ b) ≠ 0 := pow_ne_zero _ hP'
    have h5 : y ^ (b * b') ≠ 0 := pow_ne_zero _ hy
    rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff h5 (mul_ne_zero (mul_ne_zero h3 h5) h4)]
    ring
  have hi : IsInt p ((x / y) ^ (b * b')) := by
    rw [key]
    exact ((h1.pow b').mul (h2.pow b)).mul (isInt_natPow_p e)
  exact IsIntegral.of_pow (Nat.mul_pos hb hb') hi

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem normalize (h : IsClo p Ω)
    (hV : ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt p (x ^ b / (p : Ω) ^ a) ∧
      IsInt p ((p : Ω) ^ a / x ^ b))
    (n : ℕ) (c : ℕ → Ω) (hc : ∃ j < n, ¬ IsInt p (c j)) :
    ∃ l : Ω, IsAlgZp p l ∧ (∃ m : ℕ, 0 < m ∧ IsInt p (l ^ m / (p : Ω))) ∧
      (∀ j < n, IsInt p (l * c j)) ∧
      ∃ j < n, ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((l * c j) ^ m / (p : Ω)) := by
  classical
  have hp0 := p_ne_zero' h
  choose A B hB h1 h2 using hV
  let w : Ω → ℚ := fun x => if hx : x = 0 then 0 else (A x hx : ℚ) / B x hx
  obtain ⟨j1, hj1, hnj1⟩ := hc
  have hc1 : c j1 ≠ 0 := fun e => hnj1 (e ▸ isIntegral_zero)
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image ((Finset.range n).filter (fun j => c j ≠ 0))
    (fun j => w (c j)) ⟨j1, by simp [hj1, hc1]⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hj0 hmin
  obtain ⟨hj0n, hx0⟩ := hj0
  have hdiv : ∀ j < n, c j ≠ 0 → IsInt p (c j / c j0) := by
    intro j hj hcj
    refine isInt_div h hx0 (hB _ hcj) (hB _ hx0) (h1 _ hcj) (h2 _ hx0) ?_
    have := hmin j ⟨hj, hcj⟩
    simpa [w, hcj, hx0] using this
  have hb := hB _ hx0
  have hu := h1 _ hx0
  have hu' := h2 _ hx0
  generalize A (c j0) hx0 = a at hu hu'
  generalize B (c j0) hx0 = b at hb hu hu'
  have hxInt_of : IsInt p (c j0) → ∀ j < n, IsInt p (c j) := by
    intro hxi j hj
    by_cases hcj : c j = 0
    · rw [hcj]; exact isIntegral_zero
    · have := (hdiv j hj hcj).mul hxi
      rwa [div_mul_cancel₀ _ hx0] at this
  have ha : a < 0 := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hneg
    apply hnj1
    apply hxInt_of _ j1 hj1
    have e : c j0 ^ b = (c j0 ^ b / (p : Ω) ^ a) * (p : Ω) ^ k := by
      rw [hk, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    exact IsIntegral.of_pow hb (e ▸ hu.mul (isInt_natPow_p k))
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 ha.le)
  haveI := h.clo
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq ((p : Ω) ^ k) hb
  have hk1 : 1 ≤ k := by omega
  have hpa : (p : Ω) ^ a = ((p : Ω) ^ k)⁻¹ := by
    rw [← zpow_natCast, ← hk, zpow_neg, inv_inv]
  have hlx : (l * c j0) ^ b = c j0 ^ b / (p : Ω) ^ a := by
    rw [mul_pow, hl, hpa, div_inv_eq_mul, mul_comm]
  have hlxi : IsInt p (l * c j0) := IsIntegral.of_pow hb (hlx ▸ hu)
  refine ⟨l, ?_, ⟨b, hb, ?_⟩, ?_, j0, hj0n, ?_⟩
  · refine ⟨Polynomial.X ^ b - Polynomial.C ((p : ℤ_[p]) ^ k), Polynomial.X_pow_sub_C_ne_zero hb _, ?_⟩
    simp [hl]
  · rw [hl]
    have e : (p : Ω) ^ k / p = (p : Ω) ^ (k - 1) := by
      rw [div_eq_iff hp0, ← pow_succ, Nat.sub_add_cancel hk1]
    rw [e]
    exact isInt_natPow_p _
  · intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, mul_zero]; exact isIntegral_zero
    · have e : (c j / c j0) * (l * c j0) = l * c j := by
        rw [mul_comm l (c j0), ← mul_assoc, div_mul_cancel₀ _ hx0, mul_comm]
      exact e ▸ (hdiv j hj hcj).mul hlxi
  · rintro ⟨m, hm, hsm⟩
    apply not_isInt_inv_p h
    have hz : l * c j0 ≠ 0 := by
      intro e0
      rw [e0, zero_pow hb.ne', eq_comm, div_eq_zero_iff] at hlx
      rcases hlx with h0 | h0
      · exact hx0 (pow_eq_zero_iff hb.ne' |>.1 h0)
      · exact zpow_ne_zero _ hp0 h0
    have hinv : (p : Ω) ^ a / c j0 ^ b = ((l * c j0) ^ b)⁻¹ := by rw [hlx, inv_div]
    rw [hinv] at hu'
    obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
    have e : ((p : Ω))⁻¹ = ((l * c j0) ^ m / p) ^ (b1 + 1) * (((l * c j0) ^ (b1 + 1))⁻¹) ^ m *
        (p : Ω) ^ b1 := by
      generalize l * c j0 = z at hz
      rw [div_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm (b1 + 1) m, pow_succ (p : Ω) b1]
      have hzz : z ^ (m * (b1 + 1)) ≠ 0 := pow_ne_zero _ hz
      have hpp : (p : Ω) ^ b1 ≠ 0 := pow_ne_zero _ hp0
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ hzz, div_mul_eq_mul_div, one_mul, mul_comm _ (p : Ω),
        eq_div_iff (mul_ne_zero hp0 hpp), inv_mul_cancel_left₀ hp0]
    rw [e]
    exact ((hsm.pow _).mul (hu'.pow m)).mul (isInt_natPow_p b1)

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
    IsInt p (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt p (c j) := by
  intro p _ Ω _ _ h T N c hfix hint
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨l, hlalg, ⟨m0, hm0, hlsm⟩, hlint, j0, hj0, hj0ns⟩ :=
    normalize h (GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h) (p ^ N) c hne
  choose S hSalg hSmem using fun j => GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp p Ω h (c j) (hfix j)
  let S' : Finset Ω := insert l ((Finset.range (p ^ N)).biUnion S)
  have hS'alg : ∀ s ∈ S', IsAlgZp p s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hlalg
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hs
      exact hSalg j s hj
  set E := Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S' : Set Ω)) with hE
  have hrange : Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) :=
    fun x hx => Subfield.subset_closure (Or.inl hx)
  have hlE : l ∈ E := Subfield.subset_closure (Or.inr (Finset.mem_insert_self _ _))
  have hcE : ∀ j < p ^ N, c j ∈ E := by
    intro j hj
    refine Subfield.closure_mono ?_ (hSmem j)
    apply Set.union_subset_union_right
    intro s hs
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hs⟩)
  have hsum : (∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) =
      l * ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsmall : ∃ m : ℕ, 0 < m ∧
      IsInt p ((∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) ^ m / (p : Ω)) := by
    refine ⟨m0, hm0, ?_⟩
    rw [hsum, mul_pow, mul_div_right_comm]
    exact hlsm.mul (hint.pow m0)
  have := GlobalTheory.T.residue_tower_powers_linearIndependent p Ω h E hrange (GlobalTheory.T.towerParameter_not_pow_mod_maximalIdeal_adjoin_algebraic p Ω h S' hS'alg) T N (fun j => l * c j)
    (fun j hj => ⟨E.mul_mem hlE (hcE j hj), hlint j hj⟩) hsmall j0 hj0
  exact hj0ns this

end GlobalTheory.K5.Orth
