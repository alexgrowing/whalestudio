import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnitStatement
open GlobalTheory.K5

namespace GlobalTheory.K5.ResidueIndep

open Polynomial

theorem field_indep {k : Type} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (K : Subfield k)
    (N : ℕ) (t : k) (ha : t ^ p ^ N ∈ K) (hna : ∀ b ∈ K, b ^ p ≠ t ^ p ^ N)
    (c : ℕ → k) (hc : ∀ j < p ^ N, c j ∈ K)
    (hs : ∑ j ∈ Finset.range (p ^ N), c j * t ^ j = 0) : ∀ j < p ^ N, c j = 0 := by
  classical
  haveI : ExpChar K p := ExpChar.prime hp.out
  obtain ⟨n, y, hf⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C (F := K) p (x := t)).1
    ((minpoly.natSepDegree_eq_one_iff_pow_mem (F := K) p (x := t)).2 ⟨N, ⟨⟨_, ha⟩, rfl⟩⟩)
  have hy : t ^ p ^ n = (y : k) := by
    have := minpoly.aeval K t
    rw [hf] at this
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    exact sub_eq_zero.1 this
  have hNn : N ≤ n := by
    by_contra h
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 h)
    refine hna ((y : k) ^ p ^ r) (K.pow_mem y.2 _) ?_
    rw [← hy, ← pow_mul, ← pow_mul, pow_add, pow_add, pow_one, mul_assoc]
  let c' : ℕ → K := fun j => if h : j < p ^ N then ⟨c j, hc j h⟩ else 0
  let P : K[X] := ∑ j ∈ Finset.range (p ^ N), monomial j (c' j)
  have hP : aeval t P = 0 := by
    rw [← hs, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_monomial]
    simp only [c', dif_pos (Finset.mem_range.1 hj)]
    rfl
  have hP0 : P = 0 := by
    by_contra h
    have h1 := minpoly.degree_le_of_ne_zero K t h hP
    have h2 : P.degree < ((p ^ N : ℕ) : WithBot ℕ) := by
      refine (degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j hj
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hj)
    rw [hf, degree_X_pow_sub_C (pow_pos hp.out.pos n)] at h1
    have h3 := h1.trans_lt h2
    have h4 : p ^ n < p ^ N := by exact_mod_cast h3
    exact absurd (Nat.pow_le_pow_right hp.out.pos hNn) (not_le.2 h4)
  intro j hj
  have h1 : P.coeff j = c' j := by
    simp only [P, finset_sum_coeff, coeff_monomial]
    rw [Finset.sum_ite_eq' , if_pos (Finset.mem_range.2 hj)]
  rw [hP0, coeff_zero] at h1
  have h2 := congrArg Subtype.val h1
  simp only [c', dif_pos hj] at h2
  exact h2.symm

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_rad_iff (h : IsClo p Ω) (x : integralClosure (O0 p) Ω) :
    x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
    refine ⟨n + 1, n.succ_pos, ?_⟩
    have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
    have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
      rw [pow_succ, ← h1]; push_cast; field_simp
    rw [h2]
    exact (z * x).2
  · rintro ⟨m, -, hm⟩
    refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
    push_cast
    field_simp

theorem isInt_inv (h : IsClo p Ω) (x : Ω)
    (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt p (x ^ m / (p : Ω))) : x ≠ 0 ∧ IsInt p x⁻¹ := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpi : IsIntegral (O0 p) (p : Ω) := by exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx ⟨1, one_pos, by simpa [IsInt] using isIntegral_zero⟩
  refine ⟨hx0, ?_⟩
  obtain ⟨a, b, hb, h1, h2⟩ := GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h x hx0
  by_cases ha : 0 < a
  · exfalso
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
    refine hx ⟨b, hb, ?_⟩
    have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
      rw [zpow_natCast]; field_simp; ring
    rw [this]
    exact IsIntegral.mul h1 (hpi.pow n)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
    refine IsIntegral.of_pow hb ?_
    have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
    rw [this]
    exact IsIntegral.mul h2 (hpi.pow n)

theorem rad_isMaximal (h : IsClo p Ω) :
    (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical.IsMaximal := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Ideal.isMaximal_iff]
  constructor
  · rw [mem_rad_iff h]
    rintro ⟨m, -, hm⟩
    refine Basic.not_cong_one_zero h 1 one_ne_zero ⟨_, hm, ?_⟩
    simp [hp0]
  · intro J x _ hx hxJ
    rw [mem_rad_iff h] at hx
    obtain ⟨h0, h1⟩ := isInt_inv h _ hx
    have : (1 : integralClosure (O0 p) Ω) = ⟨_, h1⟩ * x :=
      Subtype.ext (inv_mul_cancel₀ h0).symm
    rw [this]
    exact J.mul_mem_left _ hxJ

theorem residue_indep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt p (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt p ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt p (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff h]
  haveI : M.IsMaximal := rad_isMaximal h
  letI : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  haveI : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · obtain ⟨h1, h2⟩ := isInt_inv h (y : Ω) (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dif_pos hj]
  have key := field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have := (hmem (y ^ p - t ^ p ^ N)).1 (by rw [map_sub, map_pow, map_pow, hb, sub_self])
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)

end GlobalTheory.K5.ResidueIndep
