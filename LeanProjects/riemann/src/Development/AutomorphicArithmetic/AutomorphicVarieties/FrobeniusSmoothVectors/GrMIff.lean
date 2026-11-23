import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have h : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  have s0 : sg R 0 = 1 := pow_zero _
  have s1 : sg R 1 = -1 := pow_one _
  have e : (0 : ZMod 2) - 1 = 1 := by decide
  rcases h i with rfl | rfl <;> rcases h j with rfl | rfl
  · rw [sub_self, s0, one_mul]
  · rw [e, s0, one_mul]
  · rw [sub_zero, s0, mul_one]
  · rw [sub_self, s0, s1, neg_mul_neg, one_mul]

private theorem sg_sq (R : Type) [CommRing R] (i : ZMod 2) : sg R i * sg R i = 1 := by
  rw [← sg_sub, sub_self]
  exact pow_zero _

private def sgM (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal fun a => sg R (α a)

private theorem sgM_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) : sgM R α * sgM R α = 1 := by
  simp only [sgM, Matrix.diagonal_mul_diagonal, sg_sq, Matrix.diagonal_one]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ (σ : R →+* R).mapMatrix M = sgM R α * M * sgM R β := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [sgM, sgM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  show σ (M a b) = sg R (α a - β b) * M a b ↔ σ (M a b) = _
  rw [sg_sub, mul_right_comm]

private theorem grM_mul {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β γ : Fin 3 → ZMod 2) (M N : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) (h' : GrM σ β γ N) :
    GrM σ α γ (M * N) := by
  rw [grM_iff] at h h' ⊢
  rw [map_mul, h, h']
  calc sgM R α * M * sgM R β * (sgM R β * N * sgM R γ)
      = sgM R α * M * (sgM R β * sgM R β) * N * sgM R γ := by simp only [Matrix.mul_assoc]
    _ = sgM R α * (M * N) * sgM R γ := by rw [sgM_sq, Matrix.mul_one, Matrix.mul_assoc _ M]

private theorem grM_inv {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (g : GL (Fin 3) R) (h : GrM σ α β (g : Matrix (Fin 3) (Fin 3) R)) :
    GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [grM_iff] at h ⊢
  have h1 : (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) *
      (σ : R →+* R).mapMatrix ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : sgM R β * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * sgM R α *
      (σ : R →+* R).mapMatrix (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [h]
    calc _ = sgM R β * (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (sgM R α * sgM R α) *
          (g : Matrix (Fin 3) (Fin 3) R)) * sgM R β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [sgM_sq, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, sgM_sq]
  exact (left_inv_eq_right_inv h2 h1).symm

private theorem grM_J {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) :
    GrM σ pq pq (Jmat R 3) := by
  intro a b
  unfold Jmat
  split_ifs with e
  · have : pq a - pq b = 0 := by
      subst e
      revert a
      decide
    rw [this]
    show σ 1 = sg R 0 * 1
    rw [map_one, mul_one]
    exact (pow_zero _).symm
  · exact Submodule.zero_mem _

private theorem grM_tr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) (h : GrM σ α β M) : GrM σ β α Mᵀ := by
  intro a b
  have e : σ (M b a) = sg R (α b - β a) * M b a := h b a
  show σ (M b a) = sg R (β a - α b) * M b a
  rw [e, sg_sub, sg_sub, mul_comm (sg R (α b))]

theorem UpperTheory.V.Fr.ep_grm :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R), (∀ α, GrM σ α α 1) ∧ (∀ α β M N, GrM σ α β M → GrM σ α β N → GrM σ α β (M - N)) ∧ (∀ α β γ M N, GrM σ α β M → GrM σ β γ N → GrM σ α γ (M * N)) ∧ (∀ α β (g : GL (Fin 3) R), GrM σ α β (g : Matrix (Fin 3) (Fin 3) R) → GrM σ β α ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) ∧ ∀ (e : ℤˣ) (g : GL (Fin 3) R), GrM σ pq pq (g : Matrix (Fin 3) (Fin 3) R) → GrM σ pq pq ((sgnAct 3 R e g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O R _ _ _ σ
  refine ⟨fun α => ?_, fun α β M N h h' a b => Submodule.sub_mem _ (h a b) (h' a b), grM_mul σ, grM_inv σ,
    fun e g h => ?_⟩
  · rw [grM_iff, map_one, Matrix.mul_one, sgM_sq]
  · rcases Int.units_eq_one_or e with rfl | rfl
    · rwa [sgnAct_one]
    · rw [sgnAct_neg_one, theta_val]
      exact grM_mul σ _ pq _ _ _ (grM_mul σ _ pq _ _ _ (grM_J σ) (grM_tr σ _ _ _ (grM_inv σ _ _ g h))) (grM_J σ)
