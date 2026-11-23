import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) : GL (Fin 3) B where
  val := triM t x y z
  inv := !![((t 0)⁻¹ : Bˣ), -x * ((t 0)⁻¹ : Bˣ), (x * y - z) * ((t 0)⁻¹ : Bˣ);
    0, ((t 1)⁻¹ : Bˣ), -y * ((t 1)⁻¹ : Bˣ); 0, 0, ((t 2)⁻¹ : Bˣ)]
  val_inv := by
    have h0 := (t 0).mul_inv
    have h1 := (t 1).mul_inv
    have h2 := (t 2).mul_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | linear_combination (-x) * h0
        | linear_combination (x * y - z) * h0 - x * y * h1
        | linear_combination (-y) * h1
  inv_val := by
    have h0 := (t 0).inv_mul
    have h1 := (t 1).inv_mul
    have h2 := (t 2).inv_mul
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | ring

private theorem triGL_val {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    (triGL t x y z : Matrix (Fin 3) (Fin 3) B) = triM t x y z := rfl

private theorem triGL_congr {B : Type} [CommRing B] {t s : Fin 3 → Bˣ} {x y z x' y' z' : B}
    (ht : t = s) (hx : x = x') (hy : y = y') (hz : z = z') : triGL t x y z = triGL s x' y' z' := by
  subst ht hx hy hz
  rfl

private theorem theta_triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    theta (triGL t x y z) = triGL (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  apply Units.ext
  rw [theta_val, triGL_val]
  have hinv : ((triGL t x y z)⁻¹ : GL (Fin 3) B).val =
      !![(((t 0)⁻¹ : Bˣ) : B), -x * (((t 0)⁻¹ : Bˣ) : B), (x * y - z) * (((t 0)⁻¹ : Bˣ) : B);
        0, (((t 1)⁻¹ : Bˣ) : B), -y * (((t 1)⁻¹ : Bˣ) : B); 0, 0, (((t 2)⁻¹ : Bˣ) : B)] := rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, triM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Fin.rev] <;> ring

private theorem triGL_mul {B : Type} [CommRing B] (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triGL t x y z * triGL s x' y' z' = triGL (fun i => t i * s i)
      (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
      (z + ((t 0 / t 2 : Bˣ) : B) * z' + x * (((t 1 / t 2 : Bˣ) : B) * y')) := by
  apply Units.ext
  rw [Units.val_mul, triGL_val, triGL_val, triGL_val]
  have h1 := (t 1).inv_mul
  have h2 := (t 2).inv_mul
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, triM, div_eq_mul_inv, -Units.mul_inv, -Units.inv_mul] <;>
    first
      | linear_combination (-((t 0 : B) * x' * s 1)) * h1
      | linear_combination (-((t 1 : B) * y' * s 2)) * h2
      | linear_combination (-((t 0 : B) * z' * s 2 + x * t 1 * y' * s 2)) * h2

theorem UpperTheory.exists_unipotent_from_torus_coords :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B), 2 * h = 1 → ∀ (β : G → B × B) (γ : G → B), (∀ g g', β (g * g') = β g + T.M1 g (β g')) → T.IsGam h β γ → ∃ u : G →* GG 3 B, T.Coord h β γ u := by
  intro G B _ _ η T h hh β γ hβ hγ
  let F : G → GG 3 B := fun g =>
    ⟨triGL (T.t g) (β g).1 (β g).2 (γ g + h * (β g).1 * (β g).2), η g⟩
  have hmul : ∀ g g' : G, F (g * g') = F g * F g' := by
    intro g g'
    have hab : (((T.t g 0 / T.t g 2 : Bˣ)) : B) =
        ((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) := by
      rw [← Units.val_mul, div_mul_div_cancel]
    have hb := hβ g g'
    have hc := hγ g g'
    apply SemidirectProduct.ext
    · simp only [F, SemidirectProduct.mul_left]
      rcases Int.units_eq_one_or (η g) with he | he
      · rw [he, sgnAct_one, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_pos he] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_pos he, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_pos he]
        · rw [hb]; rfl
        · rw [hb]; rfl
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_one, Int.cast_one, one_mul]
          linear_combination ((β g).1 * ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g').2) * hh
      · have hne : η g ≠ 1 := by rw [he]; decide
        rw [he, sgnAct_neg_one, theta_triGL, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_neg hne]
        · rw [hb]
          simp only [Prod.fst_add]
          ring
        · rw [hb]
          simp only [Prod.snd_add]
          ring
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_neg, Units.val_one, Int.cast_neg,
            Int.cast_one]
          linear_combination (((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) *
            (β g').1 * (β g').2 - ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g).1 * (β g').1) * hh
    · simp only [F, SemidirectProduct.mul_right, map_mul]
  refine ⟨MonoidHom.mk' F hmul, ?_⟩
  exact Tor.Coord.mk (fun g => rfl) (fun g => rfl)
