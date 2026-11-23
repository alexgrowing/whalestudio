import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem tc_perm {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : GL (Fin n) R) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w (σ i) i ≠ 0 := by
  by_contra h
  push Not at h
  have hd : (w : Matrix (Fin n) (Fin n) R).det = 0 := by
    rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    obtain ⟨i, hi⟩ := h σ
    have hp : ∏ j, (w : Matrix (Fin n) (Fin n) R) (σ j) j = 0 :=
      Finset.prod_eq_zero (f := fun j => (w : Matrix (Fin n) (Fin n) R) (σ j) j) (Finset.mem_univ i) hi
    rw [hp, smul_zero]
  have hu : IsUnit (w : Matrix (Fin n) (Fin n) R).det := (Matrix.isUnit_iff_isUnit_det _).1 w.isUnit
  exact hu.ne_zero hd

private theorem tc_inv {R : Type} [CommRing R] {n : ℕ} (w : GL (Fin n) R) (b t : Fin n → Bool)
    (h : ∀ i j, b i ≠ t j → w i j = 0) (i j : Fin n) (e : t i ≠ b j) : (w⁻¹ : GL (Fin n) R) i j = 0 := by
  classical
  set M : Matrix (Fin n) (Fin n) R := (w : Matrix (Fin n) (Fin n) R) with hM
  set N : Matrix (Fin n) (Fin n) R := ((w⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hN
  let Dt : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if t k then 1 else 0
  let Db : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun k => if b k then 1 else 0
  have hc : M * Dt = Db * M := by
    ext p q
    simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hpq : b p = t q
    · rw [hpq]; ring
    · rw [show M p q = 0 from h p q hpq]; simp
  have hNM : N * M = 1 := Units.inv_mul w
  have hMN : M * N = 1 := Units.mul_inv w
  have key : Dt * N = N * Db := by
    calc Dt * N = N * M * Dt * N := by rw [hNM, Matrix.one_mul]
      _ = N * (M * Dt) * N := by simp only [Matrix.mul_assoc]
      _ = N * (Db * M) * N := by rw [hc]
      _ = N * Db * (M * N) := by simp only [Matrix.mul_assoc]
      _ = N * Db := by rw [hMN, Matrix.mul_one]
  have hij := congrFun (congrFun key i) j
  simp only [Dt, Db, Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  cases hti : t i <;> cases hbj : b j <;> simp [hti, hbj] at hij e ⊢ <;>
    first | exact hij | exact hij.symm

private theorem tc_same {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card =
      (Finset.univ.filter fun i => t i = true).card.choose 2 +
        (Finset.univ.filter fun i => ¬ t i = true).card.choose 2 := by
  classical
  have hU : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2) =
      ((Finset.univ.filter fun i => t i = true) ×ˢ (Finset.univ.filter fun i => t i = true)).filter
          (fun p => p.1 < p.2) ∪
        ((Finset.univ.filter fun i => ¬ t i = true) ×ˢ
          (Finset.univ.filter fun i => ¬ t i = true)).filter (fun p => p.1 < p.2) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product]
    cases t x <;> cases t y <;> simp
  rw [hU, Finset.card_union_of_disjoint, Finset.card_product_filter_lt,
    Finset.card_product_filter_lt]
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2
  exact h2.1.1 h1.1.1

private theorem tc_diff {n : ℕ} (t : Fin n → Bool) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card =
      (Finset.univ.filter fun i => t i = true).card *
        (Finset.univ.filter fun i => ¬ t i = true).card := by
  classical
  have hsplit : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 = t p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ t p.1 ≠ t p.2).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact h2.2.2 h1.2.2
  have htot : (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n.choose 2 := by
    simpa using Fintype.card_product_filter_lt (α := Fin n)
  have hcard : (Finset.univ.filter fun i => t i = true).card +
      (Finset.univ.filter fun i => ¬ t i = true).card = n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hch : ∀ a b : ℕ, (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
    intro a b
    induction b with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ', Nat.choose_succ_succ' k, Nat.choose_one_right,
        Nat.choose_one_right, ih]
      ring
  have hh := hch (Finset.univ.filter fun i => t i = true).card
    (Finset.univ.filter fun i => ¬ t i = true).card
  rw [hcard] at hh
  rw [htot, tc_same t] at hsplit
  linarith

theorem UpperTheory.V.Pa.tyCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (v : F.Vl) (g : ℕ), (Finset.univ.filter fun i => x.ty v i = true).card = x.a ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 = x.ty v p.2).card + g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = nu n x.a g ∧ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2).card = x.a * (n - x.a) ∧ ∀ i j : Fin n, x.ty v i ≠ decide ((j : ℕ) < x.a) → ((x.w v)⁻¹ : GL (Fin n) x.A) i j = 0 := by
  intro l _ F n x v g
  classical
  obtain ⟨σ, hσ⟩ := tc_perm (x.w v)
  have hty : ∀ j, x.ty v j = decide (((σ j : Fin n) : ℕ) < x.a) := by
    intro j
    by_contra hne
    exact hσ j (x.w_blk v (σ j) j (Ne.symm hne))
  have hT : (Finset.univ.filter fun i => x.ty v i = true).card = x.a := by
    rw [← Fintype.card_subtype, ← Fintype.card_fin_lt_of_le x.a_le]
    refine Fintype.card_congr (Equiv.subtypeEquiv σ fun j => ?_)
    rw [hty j]
    simp
  have hF : (Finset.univ.filter fun i => ¬ x.ty v i = true).card = n - x.a := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => x.ty v i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [tc_same, tc_diff, hT, hF]
    simp [nu]
  · rw [tc_diff, hT, hF]
  · intro i j e
    exact tc_inv (x.w v) (fun k => decide ((k : ℕ) < x.a)) (x.ty v)
      (fun p q hpq => x.w_blk v p q hpq) i j e
