import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

def Bnd (r : WithZero (Multiplicative ℤ)) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) : Prop :=
  ∀ i j, Valued.v (X i j) ≤ r

theorem v_natCast_le_one (m : ℕ) : Valued.v ((m : P.adicCompletion E)) ≤ 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

variable {r s : WithZero (Multiplicative ℤ)} {X Y : Matrix (Fin N) (Fin N) (P.adicCompletion E)}

theorem bnd_add (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X + Y) := fun i j =>
  (Valuation.map_add _ _ _).trans (max_le (hX i j) (hY i j))

theorem bnd_neg (hX : Bnd r X) : Bnd r (-X) := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]; exact hX i j

theorem bnd_sub (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X - Y) := by
  rw [sub_eq_add_neg]; exact bnd_add hX (bnd_neg hY)

theorem bnd_smul (a : P.adicCompletion E) (hX : Bnd r X) : Bnd (Valued.v a * r) (a • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]; exact mul_le_mul' le_rfl (hX i j)

theorem bnd_mul (hX : Bnd r X) (hY : Bnd s Y) : Bnd (r * s) (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [Valuation.map_mul]; exact mul_le_mul' (hX i k) (hY k j)

theorem bnd_mono (h : r ≤ s) (hX : Bnd r X) : Bnd s X := fun i j => (hX i j).trans h

theorem bnd_zero : Bnd r (0 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by simp

theorem bnd_one : Bnd 1 (1 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem bnd_sum {ι : Type} (t : Finset ι) (f : ι → Matrix (Fin N) (Fin N) (P.adicCompletion E))
    (h : ∀ k ∈ t, Bnd r (f k)) : Bnd r (∑ k ∈ t, f k) := fun i j => by
  rw [Matrix.sum_apply]; exact Valuation.map_sum_le _ fun k hk => h k hk i j

theorem bnd_pow (hX : Bnd 1 X) : ∀ k : ℕ, Bnd 1 (X ^ k)
  | 0 => by rw [pow_zero]; exact bnd_one
  | k + 1 => by rw [pow_succ]; simpa only [one_mul] using bnd_mul (bnd_pow hX k) hX

theorem bnd_pow_sub (hX : Bnd 1 X) (hY : Bnd 1 Y) (hXY : Bnd r (X - Y)) :
    ∀ k : ℕ, Bnd r (X ^ k - Y ^ k)
  | 0 => by rw [pow_zero, pow_zero, sub_self]; exact bnd_zero
  | k + 1 => by
    have e : X ^ (k + 1) - Y ^ (k + 1) = X ^ k * (X - Y) + (X ^ k - Y ^ k) * Y := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [e]
    exact bnd_add (by simpa only [one_mul] using bnd_mul (bnd_pow hX k) hXY)
      (by simpa only [mul_one] using bnd_mul (bnd_pow_sub hX hY hXY k) hY)

noncomputable def tail (n : ℕ) (c : P.adicCompletion E) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
  ∑ k ∈ Finset.range (n - 1), ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) • X ^ (k + 2)

theorem v_coef_le_one (n k : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) :
    Valued.v ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) ≤ 1 := by
  rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_mul]
  exact mul_le_one' (v_natCast_le_one _) (pow_le_one' (mul_le_one' (v_natCast_le_one _) hc) _)

theorem bnd_tail (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) :
    Bnd 1 (tail n c X) :=
  bnd_sum _ _ fun k _ => bnd_mono (by simpa only [mul_one] using v_coef_le_one n k hc)
    (bnd_smul _ (bnd_pow hX _))

theorem bnd_tail_sub (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) (hY : Bnd 1 Y)
    (hXY : Bnd r (X - Y)) : Bnd r (tail n c X - tail n c Y) := by
  unfold tail
  rw [← Finset.sum_sub_distrib]
  refine bnd_sum _ _ fun k _ => ?_
  rw [← smul_sub]
  exact bnd_mono (by simpa only [one_mul] using mul_le_mul' (v_coef_le_one n k hc) (le_refl r))
    (bnd_smul _ (bnd_pow_sub hX hY hXY _))

theorem one_add_smul_pow (n : ℕ) (hn : 0 < n) (c : P.adicCompletion E)
    (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    (1 + ((n : P.adicCompletion E) * c) • X) ^ n =
      1 + ((n : P.adicCompletion E) ^ 2 * c) • (X + c • tail n c X) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [add_comm (1 : Matrix _ _ _), (Commute.one_right _).add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [tail, Nat.add_sub_cancel, smul_add, Finset.smul_sum, smul_smul, smul_pow]
  have hc : ∀ (j : ℕ) (Z : Matrix (Fin N) (Fin N) (P.adicCompletion E)),
      Z * ((j : ℕ) : Matrix (Fin N) (Fin N) (P.adicCompletion E)) = (j : P.adicCompletion E) • Z := by
    intro j Z
    rw [← Nat.cast_comm, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  simp only [hc, smul_smul]
  have hs : ∀ x ∈ Finset.range m,
      (((m + 1).choose (x + 1 + 1) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ (x + 1 + 1)) •
        X ^ (x + 1 + 1) =
      (((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c * (c * (((m + 1).choose (x + 2) : P.adicCompletion E) *
        (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ x))) • X ^ (x + 2) := by
    intro x _
    rw [show x + 1 + 1 = x + 2 by omega]
    congr 1
    ring
  rw [Finset.sum_congr rfl hs]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one,
    one_mul, one_smul]
  have e : ((m + 1 : ℕ) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) =
      ((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c := by ring
  rw [e]
  abel

end GlobalTheory.MatNthRoot

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

theorem exists_nthRoot : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N n : ℕ)
    (c : P.adicCompletion E) (A : Matrix (Fin N) (Fin N) (P.adicCompletion E)), 0 < n → Valued.v c < 1 →
    (∀ i j, Valued.v ((A - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * c)) →
    ∃ M : Matrix (Fin N) (Fin N) (P.adicCompletion E),
      (∀ i j, Valued.v ((M - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) * c)) ∧ M ^ n = A := by
  intro E _ _ P N n c A hn hc hA
  have hc1 : Valued.v c ≤ 1 := hc.le
  rcases eq_or_ne c 0 with rfl | hc0
  · refine ⟨1, fun i j => by simp, ?_⟩
    rw [one_pow]
    have hA1 : A - 1 = 0 := Matrix.ext fun i j => by
      have h := hA i j
      rwa [mul_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at h
    exact (sub_eq_zero.1 hA1).symm
  have hn0 : (n : P.adicCompletion E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set s : P.adicCompletion E := (n : P.adicCompletion E) ^ 2 * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (pow_ne_zero _ hn0) hc0
  set Y : Matrix (Fin N) (Fin N) (P.adicCompletion E) := s⁻¹ • (A - 1) with hYdef
  have hY : Bnd 1 Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    calc Valued.v s⁻¹ * Valued.v ((A - 1) i j) ≤ Valued.v s⁻¹ * Valued.v s := mul_le_mul' le_rfl (hA i j)
      _ = 1 := by rw [← Valuation.map_mul, inv_mul_cancel₀ hs0, Valuation.map_one]
  let f : Matrix (Fin N) (Fin N) (P.adicCompletion E) → Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
    fun X => Y - c • tail n c X
  have hf1 : ∀ X, Bnd 1 X → Bnd 1 (f X) := fun X hX =>
    bnd_sub hY (bnd_mono (by simpa only [mul_one] using hc1) (bnd_smul c (bnd_tail n hc1 hX)))
  have hfl : ∀ X Z r, Bnd 1 X → Bnd 1 Z → Bnd r (X - Z) → Bnd (Valued.v c * r) (f X - f Z) := by
    intro X Z r hX hZ hXZ
    have e : f X - f Z = -(c • (tail n c X - tail n c Z)) := by
      simp only [f, smul_sub]; abel
    rw [e]
    exact bnd_neg (bnd_smul c (bnd_tail_sub n hc1 hX hZ hXZ))
  have hb : ∀ k : ℕ, Bnd 1 (f^[k] 0) := by
    intro k
    induction k with
    | zero => exact bnd_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact hf1 _ ih
  have hd : ∀ k : ℕ, Bnd (Valued.v c ^ k) (f^[k + 1] 0 - f^[k] 0) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact bnd_sub (hb 1) (hb 0)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := hfl _ _ _ (hb (k + 1)) (hb k) ih
      rwa [← Function.iterate_succ_apply' f k 0, ← pow_succ'] at this
  have hcau : ∀ i j, CauchySeq fun k => (f^[k] 0) i j := by
    intro i j
    refine cauchySeq_of_le_geometric ‖c‖ 1 (Valued.toNormedField.norm_lt_one_iff.2 hc) fun k => ?_
    rw [dist_eq_norm', one_mul, ← norm_pow]
    refine Valued.toNormedField.norm_le_iff.2 ?_
    rw [Valuation.map_pow]
    have := hd k i j
    rwa [Matrix.sub_apply] at this
  choose L hL using fun i j => cauchySeq_tendsto_of_complete (hcau i j)
  set L' : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Matrix.of L with hL'
  have hT : Filter.Tendsto (fun k => f^[k] 0) Filter.atTop (nhds L') :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hL i j
  have hfc : Continuous f := by
    simp only [f, tail]
    fun_prop
  have hfix : f L' = L' := by
    have h1 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds L') :=
      hT.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds (f L')) := by
      simp only [Function.iterate_succ_apply']
      exact (hfc.tendsto L').comp hT
    exact tendsto_nhds_unique h2 h1
  have hLb : Bnd 1 L' := by
    intro i j
    have hm := (Valued.isClosed_valuationSubring (P.adicCompletion E)).mem_of_tendsto (hL i j)
      (Filter.Eventually.of_forall fun k => (Valuation.mem_valuationSubring_iff _ _).2 (hb k i j))
    exact (Valuation.mem_valuationSubring_iff _ _).1 hm
  refine ⟨1 + ((n : P.adicCompletion E) * c) • L', fun i j => ?_, ?_⟩
  · rw [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    simpa only [mul_one] using mul_le_mul' (le_refl (Valued.v ((n : P.adicCompletion E) * c))) (hLb i j)
  · rw [one_add_smul_pow n hn c L']
    have e : L' + c • tail n c L' = Y := by
      nth_rewrite 1 [← hfix]
      simp only [f]
      abel
    rw [e, hYdef, smul_smul, ← hs, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]

end GlobalTheory.MatNthRoot
