import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.Minor

theorem derivation_prod {A ι : Type*} [CommRing A] [Algebra ℂ A] [DecidableEq ι]
    (D : Derivation ℂ A A) (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ j ∈ s, ∏ i ∈ s, (if i = j then D (f i) else f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha,
      if_pos (rfl : a = a)]
    have h1 : ∏ i ∈ s, (if i = a then D (f i) else f i) = ∏ i ∈ s, f i :=
      Finset.prod_congr rfl fun i hi => if_neg (fun h => ha (by rw [← h]; exact hi))
    have h2 : ∀ j ∈ s, ∏ i ∈ insert a s, (if i = j then D (f i) else f i) =
        f a * ∏ i ∈ s, (if i = j then D (f i) else f i) := by
      intro j hj
      rw [Finset.prod_insert ha, if_neg (fun h => ha (by rw [h]; exact hj))]
    rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum]
    simp only [smul_eq_mul]
    ring

theorem derivation_det {A n : Type*} [CommRing A] [Algebra ℂ A] [DecidableEq n] [Fintype n]
    (D : Derivation ℂ A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j => D (M i j)).det := by
  have key : ∀ N : Matrix n n A,
      N.det = ∑ π : Equiv.Perm n, (Equiv.Perm.sign π : ℤ) • ∏ i, N i (π i) := by
    intro N
    rw [← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Units.smul_def]
    rfl
  rw [key M, map_sum]
  simp_rw [key, map_zsmul, derivation_prod D Finset.univ, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.updateRow_apply]
  split_ifs with h
  · subst h
    rfl
  · rfl

private theorem derivation_pow_of_eigen {A : Type*} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A)
    (x : A) (c : ℂ) (h : D x = c • x) (n : ℕ) : D (x ^ n) = ((n : ℂ) * c) • x ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, D.leibniz, ih, h]
    simp only [smul_eq_mul]
    simp only [Algebra.smul_def, map_mul, map_natCast, Nat.cast_succ, map_add, map_one]
    ring

private theorem derivation_prod_of_eigen {A ι : Type*} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A)
    (s : Finset ι) (g : ι → A) (d : ι → ℂ) (h : ∀ i, D (g i) = d i • g i) :
    D (∏ i ∈ s, g i) = (∑ i ∈ s, d i) • ∏ i ∈ s, g i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, D.leibniz, ih, h, Finset.sum_insert ha]
    simp only [smul_eq_mul]
    simp only [Algebra.smul_def, map_add]
    ring

theorem derivation_prod_pow {A ι : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (s : Finset ι) (f : ι → A) (e : ι → ℕ) (c : ι → ℂ)
    (h : ∀ i, D (f i) = c i • f i) :
    D (∏ i ∈ s, f i ^ e i) = (∑ i ∈ s, (e i : ℂ) * c i) • ∏ i ∈ s, f i ^ e i := by
  exact derivation_prod_of_eigen D s (fun i => f i ^ e i) (fun i => (e i : ℂ) * c i)
    (fun i => derivation_pow_of_eigen D (f i) (c i) (h i) (e i))

variable {σ : Type} {p r : ℕ}

def rowDer (z : Fin p × Fin r → σ) (a b : Fin p) :
    Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ k, (X (z (a, k)) : MvPolynomial σ ℂ) • pderiv (z (b, k))

theorem rowOp_eq_rowDer (z : Fin p × Fin r → σ) (a b : Fin p) (P : MvPolynomial σ ℂ) :
    rowOp ℂ z a b P = rowDer z a b P := by
  rw [GlobalTheory.Capelli.rowOp_apply]
  unfold rowDer
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]

theorem rowDer_X (z : Fin p × Fin r → σ) (hz : Function.Injective z) (a b c : Fin p) (k : Fin r) :
    rowDer z a b (X (z (c, k))) = if c = b then X (z (a, k)) else 0 := by
  classical
  rw [← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply]
  simp_rw [pderiv_X]
  rw [Finset.sum_eq_single k]
  · by_cases h : c = b
    · subst h
      simp
    · rw [if_neg h, Pi.single_apply, if_neg, mul_zero]
      intro h'
      exact h (congrArg Prod.fst (hz h'))
  · intro k' _ hk'
    rw [Pi.single_apply, if_neg, mul_zero]
    intro h'
    exact hk' (congrArg Prod.snd (hz h')).symm
  · intro h
    exact absurd (Finset.mem_univ k) h

def lead (z : Fin p × Fin r → σ) {n : ℕ} (hp : n ≤ p) (hr : n ≤ r) : MvPolynomial σ ℂ :=
  (Matrix.of fun a b : Fin n =>
    (X (z (Fin.castLE hp a, Fin.castLE hr b)) : MvPolynomial σ ℂ)).det

theorem lead_swap (z : Fin p × Fin r → σ) {n : ℕ} (hp : n ≤ p) (hr : n ≤ r) :
    lead (fun w : Fin r × Fin p => z w.swap) hr hp = lead z hp hr := by
  unfold lead
  rw [← Matrix.det_transpose]
  congr 1

private theorem coordDer_lead_eq_sum_det_replaced (z : Fin p × Fin r → σ) (hz : Function.Injective z) {n : ℕ}
    (hp : n ≤ p) (hr : n ≤ r) (a b : Fin p) :
    rowDer z a b (lead z hp hr) = ∑ i : Fin n,
      if Fin.castLE hp i = b then
        ((Matrix.of fun c d : Fin n =>
          (X (z (Fin.castLE hp c, Fin.castLE hr d)) : MvPolynomial σ ℂ)).updateRow i
            fun d => X (z (a, Fin.castLE hr d))).det
      else 0 := by
  unfold lead
  rw [derivation_det]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : Fin.castLE hp i = b
  · rw [if_pos h]
    congr 2
    funext d
    simp only [Matrix.of_apply, rowDer_X z hz, if_pos h]
  · rw [if_neg h]
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro d
    simp only [Matrix.updateRow_self, Matrix.of_apply, rowDer_X z hz, if_neg h]

theorem rowDer_lead_of_lt (z : Fin p × Fin r → σ) (hz : Function.Injective z) {n : ℕ}
    (hp : n ≤ p) (hr : n ≤ r) {a b : Fin p} (hab : a < b) :
    rowDer z a b (lead z hp hr) = (0 : ℂ) • lead z hp hr := by
  rw [coordDer_lead_eq_sum_det_replaced z hz hp hr, zero_smul]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : Fin.castLE hp i = b
  · rw [if_pos h]
    have hb : (b : ℕ) = i := by rw [← h]; rfl
    have hab' : (a : ℕ) < b := hab
    have hi : (a : ℕ) < n := by have := i.isLt; omega
    have hne : i ≠ ⟨a, hi⟩ := fun e => absurd (congrArg Fin.val e) (show (i : ℕ) ≠ a by omega)
    apply Matrix.det_zero_of_row_eq hne
    rw [Matrix.updateRow_self, Matrix.updateRow_ne hne.symm]
    funext d
    rfl
  · rw [if_neg h]

theorem rowDer_lead_self (z : Fin p × Fin r → σ) (hz : Function.Injective z) {n : ℕ}
    (hp : n ≤ p) (hr : n ≤ r) (a : Fin p) :
    rowDer z a a (lead z hp hr) = (if a.val < n then (1 : ℂ) else 0) • lead z hp hr := by
  rw [coordDer_lead_eq_sum_det_replaced z hz hp hr]
  by_cases ha : (a : ℕ) < n
  · rw [if_pos ha, one_smul, Finset.sum_eq_single ⟨a, ha⟩]
    · rw [if_pos (show Fin.castLE hp ⟨a, ha⟩ = a from rfl)]
      unfold lead
      congr 1
      exact Matrix.updateRow_eq_self _ _
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext (show (j : ℕ) = a from congrArg Fin.val h))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg ha, zero_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro h
    apply ha
    rw [← h]
    exact i.isLt

theorem telescope (α : ℕ → ℕ) (hα : Antitone α) (a m : ℕ) :
    ∑ i ∈ Finset.range m, ((α i - α (i + 1) : ℕ) : ℂ) * (if a < i + 1 then 1 else 0) =
      if a ≤ m then (α a : ℂ) - α m else 0 := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    by_cases h : a ≤ 0
    · rw [if_pos h, Nat.le_zero.mp h, sub_self]
    · rw [if_neg h]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_sub (hα (Nat.le_add_right m 1))]
    by_cases h1 : a ≤ m
    · rw [if_pos h1, if_pos (by omega : a < m + 1), if_pos (by omega : a ≤ m + 1)]
      ring
    · by_cases h2 : a = m + 1
      · rw [if_neg h1, if_neg (by omega : ¬ a < m + 1), if_pos (by omega : a ≤ m + 1), h2]
        ring
      · rw [if_neg h1, if_neg (by omega : ¬ a < m + 1), if_neg (by omega : ¬ a ≤ m + 1)]
        ring

theorem what₂ (z : Fin p × Fin r → σ) (hz : Function.Injective z) (α : ℕ → ℕ) (hα : Antitone α)
    (m : ℕ) (h0 : ∀ i, m ≤ i → α i = 0) (hp : ∀ i : Fin m, i.val + 1 ≤ p)
    (hr : ∀ i : Fin m, i.val + 1 ≤ r) :
    (∀ a b : Fin p, a < b →
      rowOp ℂ z a b (∏ i : Fin m, lead z (hp i) (hr i) ^ (α i - α (i + 1))) = 0) ∧
    ∀ a : Fin p, rowOp ℂ z a a (∏ i : Fin m, lead z (hp i) (hr i) ^ (α i - α (i + 1))) =
      (α a : ℂ) • ∏ i : Fin m, lead z (hp i) (hr i) ^ (α i - α (i + 1)) := by
  constructor
  · intro a b hab
    rw [rowOp_eq_rowDer, derivation_prod_pow (rowDer z a b) Finset.univ
      (fun i => lead z (hp i) (hr i)) (fun i => α i - α (i + 1)) (fun _ => 0)
      (fun i => rowDer_lead_of_lt z hz (hp i) (hr i) hab)]
    simp
  · intro a
    rw [rowOp_eq_rowDer, derivation_prod_pow (rowDer z a a) Finset.univ
      (fun i => lead z (hp i) (hr i)) (fun i => α i - α (i + 1))
      (fun i : Fin m => if (a : ℕ) < i.val + 1 then (1 : ℂ) else 0)
      (fun i => rowDer_lead_self z hz (hp i) (hr i) a)]
    congr 1
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ((α i - α (i + 1) : ℕ) : ℂ) * (if (a : ℕ) < i + 1 then 1 else 0)) m,
      telescope α hα a m]
    by_cases h : (a : ℕ) ≤ m
    · rw [if_pos h, h0 m le_rfl, Nat.cast_zero, sub_zero]
    · rw [if_neg h, h0 a (by omega), Nat.cast_zero]

theorem lead_ne_zero (z : Fin p × Fin r → σ) (hz : Function.Injective z) {n : ℕ}
    (hp : n ≤ p) (hr : n ≤ r) : lead z hp hr ≠ 0 := by
  classical
  intro h
  let f : σ → ℂ := fun v =>
    if ∃ i : Fin n, z (Fin.castLE hp i, Fin.castLE hr i) = v then 1 else 0
  have hf : ∀ i j : Fin n, f (z (Fin.castLE hp i, Fin.castLE hr j)) = if i = j then 1 else 0 := by
    intro i j
    simp only [f]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos ⟨i, by rw [hij]⟩]
    · rw [if_neg hij, if_neg]
      rintro ⟨k, hk⟩
      have e := hz hk
      simp only [Prod.mk.injEq] at e
      have e1 := congrArg Fin.val e.1
      have e2 := congrArg Fin.val e.2
      exact hij (Fin.ext (e1.symm.trans e2))
  have h1 := congrArg (MvPolynomial.eval f) h
  rw [map_zero] at h1
  unfold lead at h1
  rw [RingHom.map_det] at h1
  have h2 : (MvPolynomial.eval f).mapMatrix (Matrix.of fun a b : Fin n =>
      (X (z (Fin.castLE hp a, Fin.castLE hr b)) : MvPolynomial σ ℂ)) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, hf,
      Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem lead_mem (z : Fin p × Fin r → σ) {n : ℕ} (hp : n ≤ p) (hr : n ≤ r) :
    lead z hp hr ∈ supported ℂ (Set.range z) := by
  have hx : ∀ c d : Fin n, (X (z (Fin.castLE hp c, Fin.castLE hr d)) : MvPolynomial σ ℂ) ∈
      supported ℂ (Set.range z) :=
    fun c d => MvPolynomial.X_mem_supported.mpr (Set.mem_range_self _)
  let N : Matrix (Fin n) (Fin n) (supported ℂ (Set.range z)) := Matrix.of fun c d => ⟨_, hx c d⟩
  have e : lead z hp hr = ((supported ℂ (Set.range z)).val.toRingHom.mapMatrix N).det := by
    unfold lead
    congr 1
  rw [e, ← RingHom.map_det]
  exact N.det.2

theorem minorPoly_highest : ∀ (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ),
    Function.Injective z → ∀ α : ℕ → ℕ, Antitone α → (∀ i, min p r ≤ i → α i = 0) →
    minorPoly z α ≠ 0 ∧ (∀ v ∈ (minorPoly z α).vars, v ∈ Set.range z) ∧
      BlockHW z α (minorPoly z α) := by
  intro σ _ p r z hz α hα h0
  have hp : ∀ i : Fin (min p r), i.val + 1 ≤ p := fun i => by
    have := i.isLt
    have := min_le_left p r
    omega
  have hr : ∀ i : Fin (min p r), i.val + 1 ≤ r := fun i => by
    have := i.isLt
    have := min_le_right p r
    omega
  have hP : minorPoly z α = ∏ i : Fin (min p r), lead z (hp i) (hr i) ^ (α i - α (i + 1)) := by
    unfold minorPoly
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold lead
    rfl
  have hcol : ∀ k l : Fin r, colOp ℂ z k l = rowOp ℂ (fun w : Fin r × Fin p => z w.swap) k l := by
    intro k l
    rw [GlobalTheory.Capelli.rowOp_eq_colOp]
    simp only [Prod.swap_swap]
  obtain ⟨hr1, hr2⟩ := what₂ z hz α hα (min p r) h0 hp hr
  obtain ⟨hc1, hc2⟩ := what₂ (fun w : Fin r × Fin p => z w.swap)
    (fun u v h => Prod.swap_injective (hz h)) α hα (min p r) h0 hr hp
  have hQ : ∏ i : Fin (min p r), lead (fun w : Fin r × Fin p => z w.swap) (hr i) (hp i) ^
      (α i - α (i + 1)) = minorPoly z α := by
    rw [hP]
    simp only [lead_swap]
  rw [hQ] at hc1 hc2
  rw [← hP] at hr1 hr2
  refine ⟨?_, ?_, ?_⟩
  · rw [hP]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (lead_ne_zero z hz (hp i) (hr i))
  · have hmem : minorPoly z α ∈ supported ℂ (Set.range z) := by
      rw [hP]
      exact Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ (lead_mem z (hp i) (hr i)) _
    intro v hv
    exact (MvPolynomial.mem_supported.mp hmem) hv
  · unfold BlockHW
    exact ⟨hr1, fun k l hkl => by rw [hcol]; exact hc1 k l hkl, hr2,
      fun k => by rw [hcol]; exact hc2 k⟩

end GlobalTheory.JointHarm.Minor
