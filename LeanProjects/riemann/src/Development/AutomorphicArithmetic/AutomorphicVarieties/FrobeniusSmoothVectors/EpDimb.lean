import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem db_inv {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (a b : Fin 3) (e : π a ≠ pq b) :
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) b a = 0 := by
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h1 : u * g = 1 := g.inv_mul
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  let P : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if π i = π a then 1 else 0
  let Q : Matrix (Fin 3) (Fin 3) K := diagonal fun i => if pq i = π a then 1 else 0
  have hc : P * g = g * Q := by
    ext i j
    simp only [P, Q, diagonal_mul, mul_diagonal]
    by_cases c : π i = pq j
    · rw [c, mul_comm]
    · rw [h i j c, mul_zero, zero_mul]
  have hd : u * P = Q * u := by
    calc u * P = u * (P * g) * u := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Q * u := by rw [hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have := congrFun (congrFun hd b) a
  simpa [P, Q, diagonal_mul, mul_diagonal, e.symm] using this

private theorem db_ex {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (b : Fin 3) : ∃ a, π a = pq b := by
  by_contra c
  push Not at c
  have h1 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := g.inv_mul
  have := congrFun (congrFun h1 b) b
  rw [Matrix.mul_apply, Finset.sum_eq_zero fun a _ => by rw [h a b (c a), mul_zero]] at this
  simp at this

private theorem db_card {K : Type} [Field K] (g : GL (Fin 3) K) (π : Fin 3 → ZMod 2)
    (h : ∀ a b, π a ≠ pq b → (g : Matrix (Fin 3) (Fin 3) K) a b = 0) (j : ZMod 2) :
    Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} ≤
      Module.finrank K ((bor g).comap (adp K j).subtype) := by
  have h' := db_inv g π h
  set u : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hu
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) * u = 1 := g.mul_inv
  have hc : ∀ X : Matrix (Fin 3) (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) * (u * X * g) * u = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  let f : {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = j} → (bor g).comap (adp K j).subtype := fun p =>
    ⟨⟨u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K), fun a b e => by
      have : (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) a b =
          u a p.1.1 * (g : Matrix (Fin 3) (Fin 3) K) p.1.2 b := by
        rw [Matrix.mul_apply, Finset.sum_eq_single p.1.2]
        · simp
        · intro c _ hc
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
        · simp
      rw [this]
      by_cases c : π p.1.1 = pq a
      · rw [h p.1.2 b fun c' => e (by rw [pw_eq, ← c, ← c', p.2.2]), mul_zero]
      · rw [h' _ _ c, zero_mul]⟩, by
      show UpT ((g : Matrix (Fin 3) (Fin 3) K) * (u * single p.1.1 p.1.2 (1 : K) * (g : Matrix (Fin 3) (Fin 3) K)) * u)
      rw [hc]
      intro a b e
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨rfl, rfl⟩
      exact absurd p.2.1 (not_le.2 e)⟩
  refine LinearIndependent.fintype_card_le_finrank (b := f) ?_
  let L : (bor g).comap (adp K j).subtype →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
    (LinearMap.mulRight K u) ∘ₗ (LinearMap.mulLeft K (g : Matrix (Fin 3) (Fin 3) K)) ∘ₗ (adp K j).subtype ∘ₗ
      Submodule.subtype _
  refine LinearIndependent.of_comp L ?_
  have : L ∘ f = (Matrix.stdBasis K (Fin 3) (Fin 3)) ∘ Subtype.val := by
    funext p
    have := Matrix.stdBasis_eq_single (R := K) p.1.1 p.1.2
    exact (hc _).trans this.symm
  rw [this]
  exact (Matrix.stdBasis K (Fin 3) (Fin 3)).linearIndependent.comp _ Subtype.val_injective

private theorem db_counts : ∀ π : Fin 3 → ZMod 2, (∃ a, π a = 0) → (∃ a, π a = 1) →
    4 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 0} ∧
    2 ≤ Fintype.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2 ∧ π p.1 - π p.2 = 1} := by
  decide +kernel

theorem UpperTheory.V.Fr.ep_dimb :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), ∀ v, 4 ≤ Module.finrank K (B.bp 0 v) ∧ 2 ≤ Module.finrank K (B.bp 1 v) := by
  intro l _ k _ F K _ _ B π h v
  have h0 : pq 1 = 0 := by decide
  have h1 : pq 0 = 1 := by decide
  obtain ⟨c0, c1⟩ := db_counts (π v) (h0 ▸ db_ex (B.g v) (π v) (h.g v) 1) (h1 ▸ db_ex (B.g v) (π v) (h.g v) 0)
  exact ⟨c0.trans (db_card (B.g v) (π v) (h.g v) 0), c1.trans (db_card (B.g v) (π v) (h.g v) 1)⟩
