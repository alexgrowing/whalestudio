import Mathlib

noncomputable def UpperTheory.Reformulated.B.H71.wt1 :
    Fin (3 : ℕ) → ℤ :=
    fun (i : Fin (3 : ℕ)) ↦ (1 : ℤ) - (↑(↑i : ℕ) : ℤ)

theorem UpperTheory.Reformulated.B.H71.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.mul_inv, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux3.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.inv_mul, Matrix.diagonal_one]

noncomputable def UpperTheory.Reformulated.B.H71.torGL.{u_1} :
    {R : Type u_1} → [inst : CommRing R] → Rˣ → GL (Fin (3 : ℕ)) R :=
    fun {R : Type u_1} [CommRing R] (t : Rˣ) ↦
      { val := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R),
        inv := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R),
        val_inv := UpperTheory.Reformulated.B.H71.aux2 t, inv_val := UpperTheory.Reformulated.B.H71.aux3 t : (Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R)ˣ }

theorem UpperTheory.Reformulated.B.H71.aux5.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R], UpperTheory.Reformulated.B.H71.torGL (1 : Rˣ) = (1 : GL (Fin (3 : ℕ)) R) := by
  intro R _
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((1 : Rˣ) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) = 1
  simp only [one_zpow, Units.val_one, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux6.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R] (s t : Rˣ),
      UpperTheory.Reformulated.B.H71.torGL (s * t) = UpperTheory.Reformulated.B.H71.torGL s * UpperTheory.Reformulated.B.H71.torGL t := by
  intro R _ s t
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((s * t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑(s ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
      Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R))
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_zpow, Units.val_mul]

noncomputable def UpperTheory.Reformulated.B.H71.tor.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → Rˣ →* GL (Fin (3 : ℕ)) R :=
    fun (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.H71.torGL, map_one' := UpperTheory.Reformulated.B.H71.aux5 R, map_mul' := UpperTheory.Reformulated.B.H71.aux6 R :
        Rˣ →* GL (Fin (3 : ℕ)) R }

theorem UpperTheory.Reformulated.B.H71.map_tor :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (t : Aˣ),
      (Matrix.GeneralLinearGroup.map f : GL (Fin (3 : ℕ)) A → GL (Fin (3 : ℕ)) B)
          ((UpperTheory.Reformulated.B.H71.tor A : Aˣ → GL (Fin (3 : ℕ)) A) t) =
        (UpperTheory.Reformulated.B.H71.tor B : Bˣ → GL (Fin (3 : ℕ)) B) ((Units.map (↑f : A →* B) : Aˣ → Bˣ) t) := by
  intro A B _ _ f t
  apply Units.ext
  change (Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : A))).map f =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑((Units.map (f : A →* B) t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : B))
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  simp only [Function.comp_apply, ← map_zpow, Units.coe_map, MonoidHom.coe_coe]
