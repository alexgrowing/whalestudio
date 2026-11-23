import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem flagC_up_mul {X : Type} [CommRing X] {n : ℕ} {A B : Matrix (Fin n) (Fin n) X}
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) :
    (∀ i j, j < i → (A * B) i j = 0) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k j (lt_of_lt_of_le hij h), mul_zero]
  · intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k i h, mul_zero]

private theorem flagC_core {X : Type} [CommRing X] {n : ℕ} (A B S T S₁ T₁ r D : Matrix (Fin n) (Fin n) X) (d : X)
    (g a : Fin n → X) (hAS : A * S = d • (1 : Matrix (Fin n) (Fin n) X)) (hTB : T * B = d • (1 : Matrix (Fin n) (Fin n) X))
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (hg : ∀ i, A i i * B i i * g i = d * d)
    (hL : ∀ i j, j < i → (S₁ * T + S * T₁) i j = 0) (hr : ∀ i j, j < i → r i j = 0)
    (hM : ∀ i j, j < i → (S₁ * r * T + S * D * T + S * r * T₁) i j = 0)
    (hMd : ∀ i, (S₁ * r * T + S * D * T + S * r * T₁) i i = g i * a i + r i i * (S₁ * T + S * T₁) i i) :
    (∀ i j, j < i → ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i j = 0) ∧
      ∀ i, ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i i = (d * d) * a i := by
  have e1 : A * (S₁ * r * T + S * D * T + S * r * T₁) * B =
      A * S₁ * r * (T * B) + (A * S) * D * (T * B) + (A * S) * r * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have e2 : A * (S₁ * T + S * T₁) * B = A * S₁ * (T * B) + (A * S) * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have key : (d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r) =
      A * (S₁ * r * T + S * D * T + S * r * T₁) * B - A * (S₁ * T + S * T₁) * B * r := by
    rw [e1, e2, hAS, hTB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_mul, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul]
    abel
  obtain ⟨m1, m2⟩ := flagC_up_mul hA hM
  obtain ⟨m3, m4⟩ := flagC_up_mul m1 hB
  obtain ⟨l1, l2⟩ := flagC_up_mul hA hL
  obtain ⟨l3, l4⟩ := flagC_up_mul l1 hB
  obtain ⟨l5, l6⟩ := flagC_up_mul l3 hr
  rw [key]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.sub_apply, m3 i j hij, l5 i j hij, sub_zero]
  · rw [Matrix.sub_apply, m4, m2, l6, l4, l2, hMd, ← hg i]
    ring

theorem UpperTheory.V.Th.Coc.flagC :
    ∀ {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (S T : Matrix (Fin n) (Fin n) O) (Δ : Fin n → O), (∀ i, Δ i ≠ 0) → (∀ a b, b < a → S a b = 0 ∧ T a b = 0) → (∀ i, S i i = Δ i ∧ T i i = Δ i) → (∀ a b, a ≠ b → (S * T) a b = 0) → ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (S₁ T₁ : Matrix (Fin n) (Fin n) X), (∀ a b, a ≠ b → (S₁ * bar X T + bar X S * T₁) a b = 0) → ∃ Y : Matrix (Fin n) (Fin n) X, ∀ (r : Matrix (Fin n) (Fin n) O) (D : Matrix (Fin n) (Fin n) X) (a : Fin n → X), (∀ i j, j < i → r i j = 0) → (∀ i j, j < i → (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i j = 0) → (∀ i, (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i i = (Δ i * Δ i) • a i + r i i • (S₁ * bar X T + bar X S * T₁) i i) → (∀ i j, j < i → (c₁ • D - (bar X r * Y - Y * bar X r)) i j = 0) ∧ ∀ i, (c₁ • D - (bar X r * Y - Y * bar X r)) i i = c₁ • a i := by
  intro O _ _ n S T Δ hΔ hup hdg hST
  have hS : ∀ i j, j < i → S i j = 0 := fun i j h => (hup i j h).1
  have hT : ∀ i j, j < i → T i j = 0 := fun i j h => (hup i j h).2
  obtain ⟨d, e, hd, he⟩ : ∃ (d : O) (e : Fin n → O), d ≠ 0 ∧ ∀ i, Δ i * Δ i * e i = d :=
    ⟨∏ i, Δ i * Δ i, fun i => ∏ k ∈ Finset.univ.erase i, Δ k * Δ k,
      Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hΔ i) (hΔ i),
      fun i => Finset.mul_prod_erase Finset.univ (fun k => Δ k * Δ k) (Finset.mem_univ i)⟩
  have hG : S * T = Matrix.diagonal fun i => Δ i * Δ i := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [(flagC_up_mul hS hT).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2]
    · rw [hST i j h, Matrix.diagonal_apply_ne _ h]
  have hdet : S.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hS i j h)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [(hdg i).1]; exact hΔ i
  have hE : ∀ i j, j < i → Matrix.diagonal e i j = 0 := fun i j h => Matrix.diagonal_apply_ne _ h.ne'
  have h1 : S * T * Matrix.diagonal e = d • (1 : Matrix (Fin n) (Fin n) O) := by
    rw [hG, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    simp only [he]
  have h2 : T * Matrix.diagonal e * S = d • (1 : Matrix (Fin n) (Fin n) O) := by
    have h3 : S.adjugate * (S * T * Matrix.diagonal e * S) = S.det • (T * Matrix.diagonal e * S) := by
      rw [Matrix.mul_assoc S, Matrix.mul_assoc S, ← Matrix.mul_assoc S.adjugate, Matrix.adjugate_mul,
        Matrix.smul_mul, Matrix.one_mul]
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul, smul_comm] at h3
    exact (smul_right_injective _ hdet h3).symm
  have hmul : ∀ (X : Type) [CommRing X] [Algebra O X] (P Q : Matrix (Fin n) (Fin n) O),
      bar X P * bar X Q = bar X (P * Q) := fun X _ _ P Q => (Matrix.map_mul).symm
  have hone : ∀ (X : Type) [CommRing X] [Algebra O X],
      bar X (d • (1 : Matrix (Fin n) (Fin n) O)) = algebraMap O X d • (1 : Matrix (Fin n) (Fin n) X) := by
    intro X _ _
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hbar : ∀ (X : Type) [CommRing X] [Algebra O X] (P : Matrix (Fin n) (Fin n) O), (∀ i j, j < i → P i j = 0) →
      ∀ i j, j < i → bar X P i j = 0 := fun X _ _ P hP i j h => by simp [hP i j h]
  refine ⟨d * d, mul_ne_zero hd hd, fun X _ _ S₁ T₁ hL =>
    ⟨-(algebraMap O X d • (T₁ * bar X (Matrix.diagonal e * S))), fun r D a hr hM hMd => ?_⟩⟩
  have := flagC_core (bar X (T * Matrix.diagonal e)) (bar X (Matrix.diagonal e * S)) (bar X S) (bar X T) S₁ T₁ (bar X r) D
    (algebraMap O X d) (fun i => algebraMap O X (Δ i * Δ i)) a (by rw [hmul, h2, hone])
    (by rw [hmul, ← Matrix.mul_assoc, h2, hone]) (hbar X _ (flagC_up_mul hT hE).1) (hbar X _ (flagC_up_mul hE hS).1)
    (fun i => by
      change algebraMap O X ((T * Matrix.diagonal e) i i) * algebraMap O X ((Matrix.diagonal e * S) i i) * _ = _
      rw [← map_mul, ← map_mul, ← map_mul, (flagC_up_mul hT hE).2,
        (flagC_up_mul hE hS).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2, ← he i]
      congr 1
      ring)
    (fun i j h => hL i j h.ne') (hbar X r hr) hM
    (fun i => by rw [hMd i, Algebra.smul_def, Algebra.smul_def]; rfl)
  rw [← map_mul, algebraMap_smul] at this
  refine ⟨this.1, fun i => ?_⟩
  rw [this.2 i, Algebra.smul_def]
