import Mathlib

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m * UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [UpperTheory.Reformulated.B.ThetaInvolution.Jmat, Matrix.one_apply, if_true, one_mul, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun e => h e.symm), if_neg h]
  · intro k _ hk
    simp [UpperTheory.Reformulated.B.ThetaInvolution.Jmat, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m, inv := UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m, val_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux2 m,
        inv_val := UpperTheory.Reformulated.B.ThetaInvolution.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux4 g,
        inv_val := UpperTheory.Reformulated.B.ThetaInvolution.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.trInv g * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m

private theorem UpperTheory.Reformulated.B.ThetaInvolution.Jgl_mul_self.{u_1} (R : Type u_1) [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.ThetaInvolution.aux2 m)

private theorem UpperTheory.Reformulated.B.ThetaInvolution.trInv_mul.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g h : GL n R) :
    UpperTheory.Reformulated.B.ThetaInvolution.trInv (g * h) = UpperTheory.Reformulated.B.ThetaInvolution.trInv g * UpperTheory.Reformulated.B.ThetaInvolution.trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    ((g⁻¹ : GL n R) : Matrix n n R).transpose * ((h⁻¹ : GL n R) : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.ThetaInvolution.trInv_trInv.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g : GL n R) :
    UpperTheory.Reformulated.B.ThetaInvolution.trInv (UpperTheory.Reformulated.B.ThetaInvolution.trInv g) = g := by
  apply Units.ext
  change (g : Matrix n n R).transpose.transpose = (g : Matrix n n R)
  exact Matrix.transpose_transpose _

private theorem UpperTheory.Reformulated.B.ThetaInvolution.trInv_Jgl.{u_1} (R : Type u_1) [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.ThetaInvolution.trInv (UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m) = UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m).transpose = UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.ThetaInvolution.Jmat]
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun e => h (by rw [e, Fin.rev_rev]))]

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.ThetaInvolution.theta (UpperTheory.Reformulated.B.ThetaInvolution.theta g) = g := by
  intro m R _ g
  have hJ := UpperTheory.Reformulated.B.ThetaInvolution.Jgl_mul_self R m
  simp only [UpperTheory.Reformulated.B.ThetaInvolution.theta, UpperTheory.Reformulated.B.ThetaInvolution.trInv_mul, UpperTheory.Reformulated.B.ThetaInvolution.trInv_trInv,
    UpperTheory.Reformulated.B.ThetaInvolution.trInv_Jgl]
  calc _ = (UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m) * g *
        (UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.ThetaInvolution.theta (g * h) = UpperTheory.Reformulated.B.ThetaInvolution.theta g * UpperTheory.Reformulated.B.ThetaInvolution.theta h := by
  intro m R _ g h
  have hJ := UpperTheory.Reformulated.B.ThetaInvolution.Jgl_mul_self R m
  simp only [UpperTheory.Reformulated.B.ThetaInvolution.theta, UpperTheory.Reformulated.B.ThetaInvolution.trInv_mul]
  calc _ = UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.trInv g * 1 * UpperTheory.Reformulated.B.ThetaInvolution.trInv h *
        UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m := by rw [mul_one]; simp only [mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.ThetaInvolution.theta, invFun := UpperTheory.Reformulated.B.ThetaInvolution.theta, left_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux8,
        right_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux8, map_mul' := UpperTheory.Reformulated.B.ThetaInvolution.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

private theorem UpperTheory.Reformulated.B.ThetaInvolution.thetaAut_mul_self.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] :
    UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R * UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R = 1 :=
  MulEquiv.ext (fun g => UpperTheory.Reformulated.B.ThetaInvolution.aux8 g)

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R := by
  intro m R _ s t
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hn]
  · simp [hn]
  · simp [hn, UpperTheory.Reformulated.B.ThetaInvolution.thetaAut_mul_self]

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.ThetaInvolution.aux11 m R, map_mul' := UpperTheory.Reformulated.B.ThetaInvolution.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.ThetaInvolution.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R) → G →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.ThetaInvolution.GG m R → MulAut (UpperTheory.Reformulated.B.ThetaInvolution.GG m R))
              ((UpperTheory.Reformulated.B.ThetaInvolution.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.ThetaInvolution.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.ThetaInvolution.conjBy_conjBy :
    ∀ {C D : Type} [inst : CommRing C] [inst_1 : Group D] (h h' : GL (Fin (3 : ℕ)) C)
      (r : D →* UpperTheory.Reformulated.B.ThetaInvolution.GG (3 : ℕ) C),
      UpperTheory.Reformulated.B.ThetaInvolution.conjBy (h * h')⁻¹ (UpperTheory.Reformulated.B.ThetaInvolution.conjBy h r) = UpperTheory.Reformulated.B.ThetaInvolution.conjBy h'⁻¹ r := by
  intro C D _ _ h h' r
  ext1 x
  have e1 : (UpperTheory.Reformulated.B.ThetaInvolution.ofGL (h * h')⁻¹ : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) =
      (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h * UpperTheory.Reformulated.B.ThetaInvolution.ofGL h')⁻¹ := by rw [map_inv, map_mul]
  have e2 : (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h'⁻¹ : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) =
      (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h')⁻¹ := map_inv _ _
  change MulAut.conj (UpperTheory.Reformulated.B.ThetaInvolution.ofGL (h * h')⁻¹)
      (MulAut.conj (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h) (r x)) =
    MulAut.conj (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h'⁻¹) (r x)
  rw [e1, e2]
  generalize (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) = a
  generalize (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h' : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) = b
  generalize r x = y
  simp only [MulAut.conj_apply]
  group
