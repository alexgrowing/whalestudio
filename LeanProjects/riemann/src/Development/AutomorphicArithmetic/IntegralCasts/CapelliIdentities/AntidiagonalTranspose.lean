import Mathlib

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m, inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m, val_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2 m,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux4 g,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat_transpose.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m).transpose = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m := by
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat]
  have : (i = j.rev) ↔ (j = i.rev) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2 m)

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_inv.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m)⁻¹ = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m :=
  inv_eq_of_mul_eq_one_left (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self m)

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_mul.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g h : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv (g * h) = UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_trInv.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv (UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g) = g := by
  apply Units.ext
  change (↑(UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g)⁻¹ : Matrix n n R).transpose = ↑g
  change ((↑g : Matrix n n R).transpose).transpose = ↑g
  exact Matrix.transpose_transpose _

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_Jgl.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m := by
  apply Units.ext
  change (((UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m)⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).transpose =
    UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m
  rw [UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_inv]
  exact UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat_transpose m

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.AntidiagonalTranspose.theta (UpperTheory.Reformulated.B.AntidiagonalTranspose.theta g) = g := by
  intro m R _ g
  have hJ := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self (R := R) m
  simp only [UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_mul, UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_trInv,
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_Jgl]
  calc _ = (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) * g *
        (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) *
        (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) := by
        simp only [hJ, mul_one, one_mul]
        simp only [mul_assoc, hJ, mul_one]
        simp only [← mul_assoc, hJ, one_mul]
    _ = g := by simp [hJ]

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.AntidiagonalTranspose.theta (g * h) = UpperTheory.Reformulated.B.AntidiagonalTranspose.theta g * UpperTheory.Reformulated.B.AntidiagonalTranspose.theta h := by
  intro m R _ g h
  have hJ := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self (R := R) m
  simp only [UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_mul]
  calc _ = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g * 1 * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv h *
        UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m := by simp only [mul_one, mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, invFun := UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, left_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8,
        right_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8, map_mul' := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut_sq.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R * UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R = 1 := by
  ext1 g
  exact UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8 g

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R := by
  intro m R _ s t
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · simp [UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut_sq]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux11 m R, map_mul' := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.AntidiagonalTranspose.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) → G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R → MulAut (UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R))
              ((UpperTheory.Reformulated.B.AntidiagonalTranspose.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.conj_right :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.AntidiagonalTranspose.conjBy h r : G → UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) g).right = ((r : G → UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) g).right := by
  intro G R _ _ m h r g
  simp [UpperTheory.Reformulated.B.AntidiagonalTranspose.conjBy, MulAut.conj_apply]
