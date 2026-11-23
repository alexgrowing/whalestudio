import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
open ReciprocityTheory.PGsh MvPolynomial

namespace GlobalTheory.DetPowDegree

variable {α : Type} [Fintype α]

def Good (l : ℤ) (L E n d s : ℕ) (p : MvPolynomial (α ⊕ α) ℤ) : Prop :=
  ∀ m : (α ⊕ α) →₀ ℕ, coeff m p ≠ 0 → (∑ q, m (Sum.inr q)) ≤ n ∧
    (∑ q, m (Sum.inl q)) + L * ∑ q, m (Sum.inr q) = d ∧
    l ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ coeff m p

variable {l : ℤ} {L E : ℕ}

theorem Good.dvd {n d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (h : Good l L E n d s p)
    (m : (α ⊕ α) →₀ ℕ) :
    l ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ coeff m p := by
  by_cases hm : coeff m p = 0
  · rw [hm]; exact dvd_zero _
  · exact (h m hm).2.2

theorem Good.zero {n d s : ℕ} : Good (α := α) l L E n d s 0 := fun m hm => by simp at hm

theorem Good.mono {n n' d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (h : Good l L E n d s p)
    (hn : n ≤ n') : Good l L E n' d s p :=
  fun m hm => ⟨(h m hm).1.trans hn, (h m hm).2⟩

theorem Good.add {n d s : ℕ} {p q : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p)
    (hq : Good l L E n d s q) : Good l L E n d s (p + q) := by
  intro m hm
  rw [coeff_add] at hm ⊢
  have h3 := dvd_add (hp.dvd m) (hq.dvd m)
  by_cases h : coeff m p = 0
  · have h' : coeff m q ≠ 0 := by simpa [h] using hm
    exact ⟨(hq m h').1, (hq m h').2.1, h3⟩
  · exact ⟨(hp m h).1, (hp m h).2.1, h3⟩

theorem Good.neg {n d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p) :
    Good l L E n d s (-p) := by
  intro m hm
  rw [coeff_neg] at hm ⊢
  have h : coeff m p ≠ 0 := by simpa using hm
  exact ⟨(hp m h).1, (hp m h).2.1, (hp m h).2.2.neg_right⟩

theorem Good.sub {n d s : ℕ} {p q : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p)
    (hq : Good l L E n d s q) : Good l L E n d s (p - q) := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

theorem Good.mul {n d s n' d' s' : ℕ} {p q : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p)
    (hq : Good l L E n' d' s' q) : Good l L E (n + n') (d + d') (s + s') (p * q) := by
  classical
  intro m hm
  rw [coeff_mul] at hm ⊢
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have h1 := hp _ (left_ne_zero_of_mul hx0)
  have h2 := hq _ (right_ne_zero_of_mul hx0)
  have key : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal m, ∀ f : α → α ⊕ α,
      (∑ q, m (f q)) = (∑ q, y.1 (f q)) + ∑ q, y.2 (f q) := by
    intro y hy f
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    rw [← hy, ← Finset.sum_add_distrib]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [key x hx]; omega
  · rw [key x hx, key x hx Sum.inr, ← h1.2.1, ← h2.2.1]; ring
  · refine Finset.dvd_sum fun y hy => ?_
    refine dvd_trans ?_ (mul_dvd_mul (hp.dvd y.1) (hq.dvd y.2))
    rw [← pow_add, key y hy Sum.inr]
    apply pow_dvd_pow
    rw [mul_add]
    omega

theorem Good.C (a : ℤ) : Good (α := α) l L E 0 0 0 (C a) := by
  classical
  intro m hm
  rw [coeff_C] at hm
  have h : 0 = m := by
    by_contra h
    simp [h] at hm
  subst h
  simp

theorem Good.pow {n d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p) (k : ℕ) :
    Good l L E (n * k) (d * k) (s * k) (p ^ k) := by
  induction k with
  | zero => simpa using Good.C (α := α) (l := l) (L := L) (E := E) 1
  | succ k ih => rw [pow_succ]; simpa only [mul_add, mul_one] using ih.mul hp

theorem Good.sum {ι : Type} {n d s : ℕ} (t : Finset ι) (f : ι → MvPolynomial (α ⊕ α) ℤ)
    (h : ∀ i ∈ t, Good l L E n d s (f i)) : Good l L E n d s (∑ i ∈ t, f i) :=
  Finset.sum_induction f _ (fun _ _ => Good.add) Good.zero h

theorem Good.prod {ι : Type} {n d : ℕ} (t : Finset ι) (f : ι → MvPolynomial (α ⊕ α) ℤ)
    (h : ∀ i ∈ t, Good l L E n d 0 (f i)) :
    Good l L E (t.card * n) (t.card * d) 0 (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Good.C (α := α) (l := l) (L := L) (E := E) 1
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_mul, add_mul, one_mul, one_mul,
      add_comm, add_comm _ d]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Good.det {k n d : ℕ} (M : Matrix (Fin k) (Fin k) (MvPolynomial (α ⊕ α) ℤ))
    (h : ∀ i j, Good l L E n d 0 (M i j)) : Good l L E (k * n) (k * d) 0 M.det := by
  rw [Matrix.det_apply']
  refine Good.sum _ _ fun σ _ => ?_
  have h1 := Good.prod (l := l) (L := L) (E := E) (n := n) (d := d) Finset.univ
    (fun i => M (σ i) i) (fun i _ => h _ _)
  have h2 := (Good.C (α := α) (l := l) (L := L) (E := E) (Equiv.Perm.sign σ : ℤ)).mul h1
  simpa using h2

theorem Good.X_inl (a : α) : Good l L E 0 1 0 (X (Sum.inl a) : MvPolynomial (α ⊕ α) ℤ) := by
  classical
  intro m hm
  rw [coeff_X'] at hm
  have h : Finsupp.single (Sum.inl a) 1 = m := by
    by_contra h
    simp [h] at hm
  subst h
  simp [Finsupp.single_apply]

theorem Good.C_mul_X_inr (a : α) :
    Good l L E 1 L 0 (MvPolynomial.C (l ^ E) * X (Sum.inr a) : MvPolynomial (α ⊕ α) ℤ) := by
  classical
  intro m hm
  rw [coeff_C_mul, coeff_X'] at hm ⊢
  have h : Finsupp.single (Sum.inr a) 1 = m := by
    by_contra h
    simp [h] at hm
  subst h
  simp [Finsupp.single_apply]

def freeIdeal (α : Type) [Fintype α] (l : ℤ) : Ideal (MvPolynomial (α ⊕ α) ℤ) where
  carrier := {p | ∀ m : (α ⊕ α) →₀ ℕ, (∑ q, m (Sum.inr q)) = 0 → l ∣ coeff m p}
  add_mem' := fun {p q} hp hq m hm => by
    rw [coeff_add]; exact dvd_add (hp m hm) (hq m hm)
  zero_mem' := fun m _ => by simp
  smul_mem' := fun c p hp m hm => by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.dvd_sum fun y hy => Dvd.dvd.mul_left (hp y.2 ?_) _
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    rw [← hy] at hm
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hm
    omega

theorem C_mem_freeIdeal : (MvPolynomial.C l : MvPolynomial (α ⊕ α) ℤ) ∈ freeIdeal α l := by
  classical
  intro m _
  rw [coeff_C]
  split_ifs <;> simp

theorem X_inr_mem_freeIdeal (a : α) :
    (X (Sum.inr a) : MvPolynomial (α ⊕ α) ℤ) ∈ freeIdeal α l := by
  classical
  intro m hm
  rw [coeff_X']
  split_ifs with h
  · subst h
    simp [Finsupp.single_apply] at hm
  · simp

theorem Good.of_mem {n d : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d 0 p)
    (h : p ∈ freeIdeal α l) : Good l L E n d 1 p := by
  intro m hm
  refine ⟨(hp m hm).1, (hp m hm).2.1, ?_⟩
  by_cases h0 : (∑ q, m (Sum.inr q)) = 0
  · simpa [h0] using h m h0
  · have h1 : 1 - (∑ q, m (Sum.inr q)) = 0 - (∑ q, m (Sum.inr q)) := by omega
    rw [h1]; exact (hp m hm).2.2

theorem C_dvd_expand_sub_pow {σ : Type} (l i : ℕ) (hl : l.Prime) (f : MvPolynomial σ ℤ) :
    MvPolynomial.C (l : ℤ) ∣ expand (l ^ i) f - f ^ (l ^ i) := by
  haveI := Fact.mk hl
  rw [C_dvd_iff_zmod, map_sub, map_expand, map_pow, sub_eq_zero]
  generalize map (Int.castRingHom (ZMod l)) f = g
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, mul_comm, expand_mul, ih, expand_zmod, ← pow_mul, mul_comm]

end GlobalTheory.DetPowDegree

namespace GlobalTheory

open DetPowDegree in

theorem det_frobenius_sub_pow_support :
  (∀ (l i E n₀ s : ℕ), l.Prime → 1 ≤ i → ∀ ψ : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ,
    ψ = (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ)).det -
      MvPolynomial.rename Sum.inl (cayDet n₀ ℤ) ^ (l ^ i) →
    ∀ m ∈ (ψ ^ s).support, (∑ q, m (Sum.inr q)) ≤ n₀ * s ∧ (∑ q, m (Sum.inl q)) + l ^ i * ∑ q, m (Sum.inr q) = n₀ * l ^ i * s ∧
      (l : ℤ) ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ MvPolynomial.coeff m (ψ ^ s)) := by
  intro l i E n₀ s hl _ ψ hψ
  set f : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ :=
    MvPolynomial.rename Sum.inl (cayDet n₀ ℤ) with hf
  have hfdet : f = (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) :
      MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ)).det := by
    rw [hf, cayDet, AlgHom.map_det]
    congr 1
    ext b c : 2
    simp [Matrix.mvPolynomialX]
  have h0 : Good (l : ℤ) (l ^ i) E n₀ (n₀ * l ^ i) 0 ψ := by
    rw [hψ]
    refine Good.sub ?_ ?_
    · have := Good.det (l := (l : ℤ)) (L := l ^ i) (E := E) (n := 1) (d := l ^ i)
        (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ))
        (fun b c => by
          refine Good.sub ?_ (Good.C_mul_X_inr _)
          have := (Good.X_inl (l := (l : ℤ)) (L := l ^ i) (E := E) (b, c)).pow (l ^ i)
          simp only [zero_mul, one_mul] at this
          exact this.mono zero_le_one)
      rwa [mul_one] at this
    · have := (Good.det (l := (l : ℤ)) (L := l ^ i) (E := E) (n := 0) (d := 1)
        (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) :
          MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ))
        (fun b c => Good.X_inl _)).pow (l ^ i)
      rw [← hfdet] at this
      simp only [mul_zero, zero_mul, mul_one] at this
      exact this.mono (Nat.zero_le _)
  have hmem : ψ ∈ freeIdeal (Fin n₀ × Fin n₀) (l : ℤ) := by
    have h2 : expand (l ^ i) f - f ^ (l ^ i) ∈ freeIdeal (Fin n₀ × Fin n₀) (l : ℤ) :=
      Ideal.mem_of_dvd _ (C_dvd_expand_sub_pow l i hl f) C_mem_freeIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h2 ⊢
    rw [← h2, hψ, map_sub, map_sub]
    congr 1
    rw [hfdet, AlgHom.map_det, RingHom.map_det, RingHom.map_det]
    congr 1
    ext b c
    have h3 := Ideal.Quotient.eq_zero_iff_mem.2
      (X_inr_mem_freeIdeal (l := (l : ℤ)) (b, c))
    simp only [RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      expand_X, map_sub, map_mul, h3, mul_zero, sub_zero]
  have h1 := (h0.of_mem hmem).pow s
  rw [one_mul] at h1
  intro m hm
  exact h1 m (mem_support_iff.1 hm)

end GlobalTheory
