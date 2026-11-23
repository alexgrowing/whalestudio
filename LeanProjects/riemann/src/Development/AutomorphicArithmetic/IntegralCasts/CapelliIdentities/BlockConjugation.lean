import Mathlib

noncomputable def UpperTheory.Reformulated.B.BlockConjugation.HasFlag :
    {H k : Type} → [inst : Group H] → [inst_1 : CommRing k] → {n : ℕ} → (H →* GL (Fin n) k) → (Fin n → H →* kˣ) → Prop :=
    fun {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ) ↦
      ∃ (g : GL (Fin n) k),
        ∀ (s : H),
          (∀ (i j : Fin n), j < i → (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i j = (0 : k)) ∧
            ∀ (i : Fin n),
              (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i i = (↑((κ i : H → kˣ) s) : k)

private def UpperTheory.Reformulated.B.BlockConjugation.blk {k : Type} [CommRing k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i)))

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_mul {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) :
    UpperTheory.Reformulated.B.BlockConjugation.blk A * UpperTheory.Reformulated.B.BlockConjugation.blk B = UpperTheory.Reformulated.B.BlockConjugation.blk (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_one {k : Type} [CommRing k] {n : ℕ} :
    UpperTheory.Reformulated.B.BlockConjugation.blk (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.one_apply, (Fin.succ_ne_zero _).symm]

private theorem UpperTheory.Reformulated.B.BlockConjugation.exists_col {k : Type} [Field k] {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ Q : GL (Fin (n + 1)) k, ∀ i, (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 = v i := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  have hd : (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)).det ≠ 0 := by
    rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ (by simpa using ha)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 a)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, fun i => ?_⟩
  change (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)) i 0 = v i
  simp

private theorem UpperTheory.Reformulated.B.BlockConjugation.conj_blk {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : ∀ i : Fin n, M i.succ 0 = 0) :
    (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) 0 0 = M 0 0 ∧
    (∀ i : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ 0 = 0) ∧
    (∀ i j : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ j.succ =
      (A * M.submatrix Fin.succ Fin.succ * B) i j) := by
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩ <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ, hM]

theorem UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline :
    ∀ {H k : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : Field k] [inst_3 : TopologicalSpace k]
      [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + (1 : ℕ))) k) (κ : Fin (n + (1 : ℕ)) → H →* kˣ)
      (v : Fin (n + (1 : ℕ)) → k),
      Continuous (⇑r : H → GL (Fin (n + (1 : ℕ))) k) →
        v ≠ (0 : Fin (n + (1 : ℕ)) → k) →
          (∀ (g : H),
              (↑((r : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k).mulVec v =
                (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k) • v) →
            ∃ (p : GL (Fin (n + (1 : ℕ))) k) (r₁ : H →* GL (Fin (n + (1 : ℕ))) k) (r' : H →* GL (Fin n) k),
              (∀ (g : H), (r₁ : H → GL (Fin (n + (1 : ℕ))) k) g = p * (r : H → GL (Fin (n + (1 : ℕ))) k) g * p⁻¹) ∧
                Continuous (⇑r₁ : H → GL (Fin (n + (1 : ℕ))) k) ∧
                  Continuous (⇑r' : H → GL (Fin n) k) ∧
                    (∀ (g : H) (i : Fin n),
                        (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) i.succ
                            (0 : Fin (n + (1 : ℕ))) =
                          (0 : k)) ∧
                      (∀ (g : H),
                          (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                              (0 : Fin (n + (1 : ℕ))) (0 : Fin (n + (1 : ℕ))) =
                            (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k)) ∧
                        (∀ (g : H) (i j : Fin n),
                            (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                                i.succ j.succ =
                              (↑((r' : H → GL (Fin n) k) g) : Matrix (Fin n) (Fin n) k) i j) ∧
                          ((UpperTheory.Reformulated.B.BlockConjugation.HasFlag r' fun (i : Fin n) ↦ κ i.succ) → UpperTheory.Reformulated.B.BlockConjugation.HasFlag r κ) := by
  intro H k _ _ _ _ _ n r κ v hr hv hev
  obtain ⟨Q, hQ⟩ := UpperTheory.Reformulated.B.BlockConjugation.exists_col v hv
  let r₁ : H →* GL (Fin (n + 1)) k := (MulAut.conj Q⁻¹).toMonoidHom.comp r
  have hr₁ : ∀ g, r₁ g = Q⁻¹ * r g * Q⁻¹⁻¹ := fun g => rfl
  have hc₁ : Continuous r₁ := by
    have : (⇑r₁) = fun g => Q⁻¹ * r g * Q⁻¹⁻¹ := funext hr₁
    rw [this]
    exact (continuous_const.mul hr).mul continuous_const
  have hQv : (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) = v := by
    ext i
    simp [hQ]
  have hcol : ∀ g i, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 =
      ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) i := by
    intro g i
    have h1 : (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) =
        ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) := by
      rw [hr₁, inv_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQv, hev,
        Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h1]
    simp
  have h0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0 := by
    intro g i
    rw [hcol]
    simp
  have h00 : ∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k) := by
    intro g
    rw [hcol]
    simp
  let φ : H →* Matrix (Fin n) (Fin n) k :=
    { toFun := fun g => (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ
      map_one' := by
        ext i j
        simp [Matrix.one_apply]
      map_mul' := fun a b => by
        ext i j
        rw [map_mul, Units.val_mul]
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, h0, zero_mul, zero_add] }
  have hφ : ∀ g, φ g = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ := fun g => rfl
  refine ⟨Q⁻¹, r₁, φ.toHomUnits, hr₁, hc₁, ?_, h0, h00, fun g i j => rfl, ?_⟩
  · rw [Units.continuous_iff]
    refine ⟨(Units.continuous_val.comp hc₁).matrix_submatrix _ _, ?_⟩
    have : (fun g => (((φ.toHomUnits g)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ) : Matrix (Fin n) (Fin n) k)) =
        fun g => (((r₁ g)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix
          Fin.succ Fin.succ := by
      funext g
      rw [← map_inv, ← map_inv]
      rfl
    rw [this]
    exact (Units.continuous_coe_inv.comp hc₁).matrix_submatrix _ _
  · rintro ⟨a, ha⟩
    let b : GL (Fin (n + 1)) k :=
      ⟨UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k),
        UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.mul_inv, UpperTheory.Reformulated.B.BlockConjugation.blk_one],
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.inv_mul, UpperTheory.Reformulated.B.BlockConjugation.blk_one]⟩
    refine ⟨b * Q⁻¹, fun s => ?_⟩
    have e : ((b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k) * (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
          UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      have : b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ = b * r₁ s * b⁻¹ := by
        rw [hr₁]
        group
      rw [this]
      rfl
    obtain ⟨c1, c2, c3⟩ := UpperTheory.Reformulated.B.BlockConjugation.conj_blk (a : Matrix (Fin n) (Fin n) k)
      ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) _ (h0 s)
    obtain ⟨d1, d2⟩ := ha s
    have e' : ((a * φ.toHomUnits s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (a : Matrix (Fin n) (Fin n) k) *
          (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ *
          ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := rfl
    rw [e'] at d1 d2
    rw [e]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · intro h
        exact absurd h (Fin.not_lt_zero _)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact c2 i
        · intro h
          rw [c3]
          exact d1 i j (Fin.succ_lt_succ_iff.mp h)
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [c1, h00]
      · rw [c3]
        exact d2 i
