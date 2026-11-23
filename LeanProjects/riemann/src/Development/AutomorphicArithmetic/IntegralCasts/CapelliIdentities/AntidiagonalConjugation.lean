import Mathlib

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, hb]
  · simp

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4 g,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m)

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m).transpose = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat]
  refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro rfl <;> simp

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g) = g := by
  intro m R _ g
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl]
  rw [mul_assoc, mul_assoc, mul_assoc, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, mul_one, ← mul_assoc,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g * UpperTheory.Reformulated.B.AntidiagonalConjugation.theta h := by
  intro m R _ g h
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m), UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, invFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, left_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8,
        right_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R * UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11 m R, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) → G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R → MulAut (UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R))
              ((UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy h r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left *
          ((UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h * r g * (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h)⁻¹).left = _
  rw [← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, one_mul,
    MulAut.one_apply]
