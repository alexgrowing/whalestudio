import Mathlib

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.SignActionTheta.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.SignActionTheta.Jmat R m * UpperTheory.Reformulated.B.SignActionTheta.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [UpperTheory.Reformulated.B.SignActionTheta.Jmat, Matrix.mul_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev, Matrix.one_apply]
  simp only [eq_comm]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, inv := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux2 m,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux4 g,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m

private theorem UpperTheory.Reformulated.B.SignActionTheta.J_mul_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.SignActionTheta.aux2 m)

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (g * h) = UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m).transpose = UpperTheory.Reformulated.B.SignActionTheta.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.SignActionTheta.Jmat]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl <;> rw [h, Fin.rev_rev]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.SignActionTheta.theta (UpperTheory.Reformulated.B.SignActionTheta.theta g) = g := by
  intro m R _ g
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv,
    UpperTheory.Reformulated.B.SignActionTheta.trInv_J]
  simp only [← mul_assoc]
  rw [UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul, mul_assoc, UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, mul_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.SignActionTheta.theta (g * h) = UpperTheory.Reformulated.B.SignActionTheta.theta g * UpperTheory.Reformulated.B.SignActionTheta.theta h := by
  intro m R _ g h
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.trInv h * _),
    UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.SignActionTheta.theta, invFun := UpperTheory.Reformulated.B.SignActionTheta.theta, left_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8,
        right_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.SignActionTheta.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R := by
  intro m R _ s t
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · rw [if_pos (by simp), if_neg hne]
    ext1 g
    exact (UpperTheory.Reformulated.B.SignActionTheta.aux8 g).symm

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.SignActionTheta.aux11 m R, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R] ℤˣ

private theorem UpperTheory.Reformulated.B.SignActionTheta.map_theta {m : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.theta g) =
      UpperTheory.Reformulated.B.SignActionTheta.theta (Matrix.GeneralLinearGroup.map f g) := by
  have hJ : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl S m := by
    ext i j
    change f (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m i j) = UpperTheory.Reformulated.B.SignActionTheta.Jmat S m i j
    unfold UpperTheory.Reformulated.B.SignActionTheta.Jmat
    split_ifs <;> simp
  have hT : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.trInv g) =
      UpperTheory.Reformulated.B.SignActionTheta.trInv (Matrix.GeneralLinearGroup.map f g) := by
    ext i j
    rfl
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [map_mul, map_mul, hJ, hT]

theorem UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm.{u_1, u_2} :
    ∀ {m : ℕ} {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S) (s : ℤˣ),
      (Matrix.GeneralLinearGroup.map f).comp
          (MulEquiv.toMonoidHom ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) s)) =
        (MulEquiv.toMonoidHom
              ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S : ℤˣ → MulAut (GL (Fin m) S)) ((MonoidHom.id ℤˣ : ℤˣ → ℤˣ) s))).comp
          (Matrix.GeneralLinearGroup.map f) := by
  intro m R S _ _ f s
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · ext1 g
    simp
  · have h1 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R :=
      if_neg (t := (1 : MulAut (GL (Fin m) R))) hne
    have h2 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m S :=
      if_neg (t := (1 : MulAut (GL (Fin m) S))) hne
    rw [MonoidHom.id_apply, h1, h2]
    refine MonoidHom.ext fun g => ?_
    exact UpperTheory.Reformulated.B.SignActionTheta.map_theta f g

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.map.{u_1, u_2} :
    {m : ℕ} →
      {R : Type u_1} →
        {S : Type u_2} →
          [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → UpperTheory.Reformulated.B.SignActionTheta.GG m R →* UpperTheory.Reformulated.B.SignActionTheta.GG m S :=
    fun {m : ℕ} {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] (f : R →+* S) ↦
      SemidirectProduct.map (Matrix.GeneralLinearGroup.map f) (MonoidHom.id ℤˣ) (UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm f)

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) → G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.SignActionTheta.GG m R → MulAut (UpperTheory.Reformulated.B.SignActionTheta.GG m R))
              ((UpperTheory.Reformulated.B.SignActionTheta.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.SignActionTheta.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.SignActionTheta.map_conjBy :
    ∀ {G R S : Type} [inst : Group G] [inst_1 : CommRing R] [inst_2 : CommRing S] {m : ℕ} (f : R →+* S) (h : GL (Fin m) R)
      (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R),
      (UpperTheory.Reformulated.B.SignActionTheta.map f).comp (UpperTheory.Reformulated.B.SignActionTheta.conjBy h r) =
        UpperTheory.Reformulated.B.SignActionTheta.conjBy ((Matrix.GeneralLinearGroup.map f : GL (Fin m) R → GL (Fin m) S) h)
          ((UpperTheory.Reformulated.B.SignActionTheta.map f).comp r) := by
  intro G R S _ _ _ m f h r
  refine MonoidHom.ext fun x => ?_
  have hi : UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h) =
      UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) :=
    SemidirectProduct.map_inl _ _ _ h
  change UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h * r x * (UpperTheory.Reformulated.B.SignActionTheta.ofGL h)⁻¹) =
    UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) * UpperTheory.Reformulated.B.SignActionTheta.map f (r x) *
      (UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h))⁻¹
  rw [map_mul, map_mul, map_inv, hi]
