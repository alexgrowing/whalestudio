import Mathlib

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  simp only [eq_comm]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m, inv := UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m, val_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m,
        inv_val := UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux4 g,
        inv_val := UpperTheory.Reformulated.B.TransposeInverseTheta.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (g * h) = UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose = (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g) = g := by
  apply Units.ext
  change (↑g : Matrix n n R).transpose.transpose = ↑g
  rw [Matrix.transpose_transpose]

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m)

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_Jgl {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) = UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m).transpose = UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat]
  by_cases h : j = i.rev
  · have h' : i = j.rev := by rw [h, Fin.rev_rev]
    simp [h, ← h']
  · have h' : ¬ i = j.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.TransposeInverseTheta.theta (UpperTheory.Reformulated.B.TransposeInverseTheta.theta g) = g := by
  intro m R _ g
  have hJ := UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self (m := m) (R := R)
  simp only [UpperTheory.Reformulated.B.TransposeInverseTheta.theta, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_trInv,
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_Jgl]
  calc _ = (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) * g *
        (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.TransposeInverseTheta.theta (g * h) = UpperTheory.Reformulated.B.TransposeInverseTheta.theta g * UpperTheory.Reformulated.B.TransposeInverseTheta.theta h := by
  intro m R _ g h
  have hJ := UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self (m := m) (R := R)
  simp only [UpperTheory.Reformulated.B.TransposeInverseTheta.theta, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul]
  calc _ = UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * 1 * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv h *
        UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m := by simp only [mul_assoc, one_mul]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.TransposeInverseTheta.theta, invFun := UpperTheory.Reformulated.B.TransposeInverseTheta.theta, left_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux8,
        right_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux8, map_mul' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut_mul_self (m : ℕ) (R : Type*) [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R * UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R = 1 := by
  ext1 g
  exact UpperTheory.Reformulated.B.TransposeInverseTheta.aux8 g

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R := by
  intro m R _ s t
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hne]
  · simp [hne]
  · simp [hne, UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut_mul_self]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux11 m R, map_mul' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) → G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R → MulAut (UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R))
              ((UpperTheory.Reformulated.B.TransposeInverseTheta.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.conj_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy h r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).left *
          ((UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  have e : (UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy h r) g =
      SemidirectProduct.inl h * r g * (SemidirectProduct.inl h)⁻¹ := rfl
  rw [e, ← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
  simp [mul_assoc]
