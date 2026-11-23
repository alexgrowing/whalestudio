import Mathlib

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m * UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, hb]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m, inv := UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m, val_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m,
        inv_val := UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux4 g,
        inv_val := UpperTheory.Reformulated.B.ConjugationByInvolution.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m * UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g * UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m * UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m)

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (g * h) = UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g * UpperTheory.Reformulated.B.ConjugationByInvolution.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose
    = (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g) = g :=
  Units.ext rfl

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_Jgl {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m) = UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m).transpose = UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m
  ext i j
  have : i = j.rev ↔ j = i.rev := by
    constructor <;> (rintro rfl; simp)
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, this]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.ConjugationByInvolution.theta (UpperTheory.Reformulated.B.ConjugationByInvolution.theta g) = g := by
  intro m R _ g
  unfold UpperTheory.Reformulated.B.ConjugationByInvolution.theta
  rw [UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul, UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul, UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_Jgl,
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_trInv, ← mul_assoc, ← mul_assoc, UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, one_mul,
    mul_assoc, UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, mul_one]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.ConjugationByInvolution.theta (g * h) = UpperTheory.Reformulated.B.ConjugationByInvolution.theta g * UpperTheory.Reformulated.B.ConjugationByInvolution.theta h := by
  intro m R _ g h
  unfold UpperTheory.Reformulated.B.ConjugationByInvolution.theta
  rw [UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m) (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m), UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, one_mul]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.ConjugationByInvolution.theta, invFun := UpperTheory.Reformulated.B.ConjugationByInvolution.theta, left_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux8,
        right_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux8, map_mul' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R * UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.ConjugationByInvolution.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux11 m R, map_mul' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.ConjugationByInvolution.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) → G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R → MulAut (UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R))
              ((UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy_right :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy h r : G → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) g).right = ((r : G → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) g).right := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL h * r g * (UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL h)⁻¹ : UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R).right = _
  rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    SemidirectProduct.right_inl, inv_one, one_mul, mul_one]
